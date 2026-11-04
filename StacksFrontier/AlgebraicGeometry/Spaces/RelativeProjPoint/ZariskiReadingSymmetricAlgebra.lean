module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SymmetricPowerTransport
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSheafifyModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafLiftSurjective

/-!
# The Zariski reading of the symmetric algebra of a quasi-coherent module

Let `T` be an object of the big fppf site and `ℱ` an `𝒪`-module on the small étale site of the
algebraic space `T` represents, with Zariski reading `ℱ_Zar` on the scheme of `T`.  The universal
property of `Sym(ℱ_Zar)` gives a comparison `Sym(ℱ_Zar) ⟶ (Sym ℱ)_Zar` of graded algebras which is
the identity in degree one.  For `ℱ` quasi-coherent it is an isomorphism in every degree: over an
affine open both sides are `Symⁿ` of the sections of `ℱ`, the sectionwise symmetric powers of a
quasi-coherent module being a sheaf on the affine étale charts.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingSymmetricAlgebraHom`: the comparison.

## Main results

* `AlgebraicGeometry.Space.bijective_zariskiReadingSymmetricAlgebraHom_app_of_isAffineOpen`: the
  comparison is bijective on the sections over an affine open, in every nonnegative degree.
* `AlgebraicGeometry.Space.symmetricAlgebraGen_comp_zariskiReadingSymmetricAlgebraHom_app_one`:
  the comparison is the identity in degree one.
* `AlgebraicGeometry.Space.isIso_zariskiReadingSymmetricAlgebraHom_app`: it is an isomorphism in
  every degree when the module is quasi-coherent.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)
  (N : SheafOfModules.{u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))

/-- The Zariski reading of the étale symmetric algebra has commuting degree-one sections. -/
theorem pairwiseCommutes_zariskiReading_symmetricAlgebraGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes
      (A := zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T) N))
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        (symmetricAlgebraGen B S hS (yonedaSpace B S hS T) N)) :=
  fun _ _ _ => eq_of_heq (symmetricAlgebra_mul_comm B S hS (yonedaSpace B S hS T) N 1 1 _ _ _)

/-- **The comparison `Sym(ℱ_Zar) ⟶ (Sym ℱ)_Zar`** from the symmetric algebra of the Zariski reading
of a module on a represented algebraic space to the Zariski reading of its symmetric algebra,
extending the identity in degree one. -/
noncomputable def zariskiReadingSymmetricAlgebraHom :
    SheafOfModules.GradedAlgebra.UnitalHom
      (Scheme.Modules.symmetricAlgebra ((BigFppfOver.toScheme B S hS).obj T)
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N))
      (zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T) N)) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra _ _).isUniversal.desc _ _
    (pairwiseCommutes_zariskiReading_symmetricAlgebraGen T N)

/-- In degree one, the comparison `zariskiReadingSymmetricAlgebraHom` composed with the inclusion
of `ℱ_Zar` into `Sym(ℱ_Zar)` is the Zariski reading of the inclusion of `ℱ` into `Sym ℱ`. -/
theorem symmetricAlgebraGen_comp_zariskiReadingSymmetricAlgebraHom_app_one :
    Scheme.Modules.symmetricAlgebraGen _ _ ≫ (zariskiReadingSymmetricAlgebraHom T N).app 1 =
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        (symmetricAlgebraGen B S hS _ N) :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra _ _).isUniversal.desc_extends _ _
    (pairwiseCommutes_zariskiReading_symmetricAlgebraGen T N)

/-- The ring map from the functions on a Zariski open of the scheme of `T` to the functions on the
étale chart it defines. -/
abbrev selfOpensSmallEtaleRingHom (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (((BigFppfOver.toScheme B S hS).obj T).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W) →+*
      ((smallEtaleRingedSite B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2).O.obj ⋙
        forget₂ CommRingCat RingCat).obj (op ((selfOpensFunctor B S hS T).obj W)) :=
  ((selfOpensStructureMap B S hS T).hom.app (op W)).hom

/-- The ring map from functions on a Zariski open to functions on its chart is bijective. -/
theorem bijective_selfOpensSmallEtaleRingHom (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Function.Bijective (selfOpensSmallEtaleRingHom T W) := by
  have hfun : (selfOpensSmallEtaleRingHom T W : _ → _) =
      ((representedSchemeStructureSheaf B S hS T).obj.map
        ((representedSmallEtaleEquivalence B S hS T).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property W)).op) ∘
        ((forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso W).inv) :=
    funext fun r => selfOpensStructureMap_hom_app T W r
  rw [hfun]
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _)

variable {T N} in
/-- **Over an affine open, the comparison is bijective in every nonnegative degree.** -/
theorem bijective_zariskiReadingSymmetricAlgebraHom_app_of_isAffineOpen
    (hN : N.IsQuasicoherentOnSite) (k : ℕ) {W : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    (hW : IsAffineOpen W) :
    Function.Bijective (((zariskiReadingSymmetricAlgebraHom T N).app (k : ℤ)).val.app (op W)) := by
  have hqc :
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N).IsQuasicoherent :=
    isQuasicoherent_zariskiReading_piece T N hN
  let φ := selfOpensSmallEtaleRingHom T W
  let e := RingEquiv.ofBijective φ (bijective_selfOpensSmallEtaleRingHom T W)
  have hψφ : ∀ r, e.symm (φ r) = r := e.symm_apply_apply
  have hφψ : ∀ s, φ (e.symm s) = s := e.apply_symm_apply
  have hW' :
      IsAffine (smallEtaleScheme B S hS (yoneda.obj T) ((selfOpensFunctor B S hS T).obj W)) := by
    show IsAffine (chartScheme ((selfOpensFunctor B S hS T).obj W))
    rw [selfOpensFunctor_obj B S hS T W]
    exact hW
  have hunitZ := Stacks.SymGraded.AffinePieces.bijective_sheafifyUnit_image_top
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) hW (k : ℤ) W
    hW.fromSpec_image_top
  have hunitE := bijective_symmetricAlgebra_sheafifyUnit_of_isAffine B S hS (yonedaSpace B S hS T)
    N hN k ((selfOpensFunctor B S hS T).obj W) hW'
  have hcomp := Stacks.GradedAlgebra.bijective_unitalHom_app_of_transport
    (O₁ := ((BigFppfOver.toScheme B S hS).obj T).sheaf.obj)
    (O₂ := (smallEtaleRingedSite B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2).O.obj)
    ((zariskiReading T (symmetricAlgebra B S hS (yonedaSpace B S hS T) N)).restrictScalars
      (𝟙 ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.obj))
    ((symmetricAlgebra B S hS (yonedaSpace B S hS T) N).restrictScalars
      (𝟙 (structureRingSheaf B S hS (yonedaSpace B S hS T)).obj))
    (X₁ := op W) (X₂ := op ((selfOpensFunctor B S hS T).obj W)) φ
    (fun _ => { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
    (fun _ _ _ _ => rfl) rfl
    ((PresheafOfModules.symPowIntGradedAlgebra.{u, u, u, u}
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N).val
        ).restrictUnitalHom
      (𝟙 ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.obj)
      (zariskiReadingSymmetricAlgebraHom T N))
    ((PresheafOfModules.symPowIntGradedAlgebra.{u, u + 1, u, u} N.val).restrictUnitalHom
      (𝟙 (structureRingSheaf B S hS (yonedaSpace B S hS T)).obj)
      (SheafOfModules.GradedAlgebra.UnitalHom.id _))
    { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (fun s => (congrArg (fun t => ((zariskiReadingSymmetricAlgebraHom T N).app 1).val.app (op W) t)
        (@Stacks.SymGraded.AffinePieces.symmetricAlgebraGen_app_eq
          ((BigFppfOver.toScheme B S hS).obj T)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) hqc W
          s).symm).trans
      ((congrArg (fun f => f.val.app (op W) s)
        (symmetricAlgebraGen_comp_zariskiReadingSymmetricAlgebraHom_app_one T N)).trans
        (symmetricAlgebraGen_app_eq N _ s)))
    k e.symm.toRingHom
    { toFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun c m => (congrArg (· • m) (hφψ c)).symm }
    hψφ hφψ (fun _ => rfl) (fun _ => rfl) Function.bijective_id
    hunitE
  exact (Function.Bijective.of_comp_iff _ hunitZ).mp hcomp

/-- **For a quasi-coherent module the comparison `Sym(ℱ_Zar) ⟶ (Sym ℱ)_Zar` is an isomorphism in
every degree.** -/
theorem isIso_zariskiReadingSymmetricAlgebraHom_app (hN : N.IsQuasicoherentOnSite) (n : ℤ) :
    IsIso ((zariskiReadingSymmetricAlgebraHom T N).app n) := by
  refine Stacks.Algebraization.isIso_of_affine_sections_bijective
    (X := (BigFppfOver.toScheme B S hS).obj T) _ fun W => ?_
  obtain k | k := n
  · exact bijective_zariskiReadingSymmetricAlgebraHom_app_of_isAffineOpen hN k W.2
  · have hn : Int.negSucc k < 0 := Int.negSucc_lt_zero k
    have h₁ : ∀ x : ((Scheme.Modules.symmetricAlgebra ((BigFppfOver.toScheme B S hS).obj T)
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N)).piece
          (Int.negSucc k)).val.obj (op W.1), x = 0 :=
      Scheme.Modules.symmetricAlgebra_piece_eq_zero _ _ _ hn _
    have h₂ : ∀ y : ((symmetricAlgebra B S hS (yonedaSpace B S hS T) N).piece
        (Int.negSucc k)).val.obj (op ((selfOpensFunctor B S hS T).obj W.1)), y = 0 :=
      @PresheafOfModules.symmetricAlgebraSheafify_piece_eq_zero.{u, u + 1, u, u} _ _
        (SmallEtale.topology B S hS (yoneda.obj T))
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj
        (structureRingSheaf B S hS (yonedaSpace B S hS T)) (𝟙 _)
        (isLocallyInjective_id_structureRingSheaf B S hS (yonedaSpace B S hS T))
        (isLocallySurjective_id_structureRingSheaf B S hS (yonedaSpace B S hS T))
        (wEqualsLocallyBijective_smallEtale B S hS (yonedaSpace B S hS T))
        (hasWeakSheafify_smallEtale B S hS (yonedaSpace B S hS T)) N.val _ hn _
    exact ⟨fun a b _ => (h₁ a).trans (h₁ b).symm, fun y => ⟨0, (h₂ _).trans (h₂ y).symm⟩⟩

end Comparison

end AlgebraicGeometry.Space
