module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalk
public import StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkTargetAction
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract

/-!
# The degree-zero term of the naive cotangent complex of a presentation is flat

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space and let
`α : E ⟶ B` be a family of generators presenting `B` as a quotient of the polynomial algebra
`A[E]`.  The degree `0` term of the naive cotangent complex `NL(α)` of that presentation is the
scalar extension `B ⊗_{A[E]} Ω_{A[E]/A}` of the relative differentials.  Its stalk at a point
`x` is the cotangent space of the presentation `Aₓ[Eₓ] → Bₓ` of the stalks, which is free on
`Eₓ`; flatness of a sheaf of modules is a stalkwise condition (Stacks 05NE), so the degree `0`
term is a flat `B`-module.

The canonical presentation, `E = B` and `α = id`, is
`Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`; the argument here is the same one,
run through the generators `Algebra.Generators.ofSurjective` of `Bₓ` over `Aₓ` given by the germs
of the generators instead of through `Algebra.Generators.self`.

## Main definitions

* `Stacks.SheafOfModules.presentationStalkGenerators`: the family of generators `Eₓ → Bₓ` of
  `Bₓ` over `Aₓ` given by the germs of `α`.
* `Stacks.SheafOfModules.presentationStalkExtensionHom` and
  `Stacks.SheafOfModules.presentationStalkExtensionInvHom`: the two morphisms of extensions of
  `Bₓ` over `Aₓ` between the stalk of `A[E] ⟶ B` and those generators.
* `Stacks.SheafOfModules.presentationTensorStalkCotangentSpaceLinearEquiv`: the identification
  of the stalk of `B ⊗_{A[E]} Ω_{A[E]/A}` with the cotangent space of those generators, linear
  over the stalk of `B`.

## Main results

* `Stacks.SheafOfModules.isFlat_presentationTensorDifferentialsSheaf`: `B ⊗_{A[E]} Ω_{A[E]/A}`
  is a flat `B`-module.
* `Stacks.SheafOfModules.isFlat_presentationNaiveCotangentComplex_X_zero`: the degree `0` term
  of `NL(α)` is a flat `B`-module.

## Implementation notes

The imports are kept to the stalk computations of the naive cotangent complex of sheaves of rings
on a space and the stalkwise criterion for flatness.  With the scheme-level stalk files of the
canonical case (`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentFlatDegreeZero`) in scope, a
stalk of the tensor-differentials sheaf written out in this file no longer unifies within the
heartbeat ceiling with the same stalk as produced by
`Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv`, so that module is not imported.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the naive cotangent
  complex of a presentation.
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE), flatness of a sheaf of
  modules is a stalkwise condition.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules (isFlat_iff_stalk_flat commStalkRingEquiv_smul_eq')
open Stacks.RelativeDifferentialStalk (algebraStalk)
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

universe u

noncomputable section

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}}
  (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (a : A ⟶ B)
  (E : T.Presheaf (Type u))
  (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology T) B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
    (presentation (Opens.grothendieckTopology T) A B a E α).hom] (x : T)

/-- The germs of the generators generate the stalk `Bₓ` as an `Aₓ`-algebra: the stalk of the
locally surjective presentation is surjective, and it is evaluation at those germs. -/
theorem aeval_presentationStalkVariable_surjective :
    letI := algebraStalk a.hom x
    Function.Surjective (MvPolynomial.aeval (R := ToType (TopCat.Presheaf.stalk A.obj x))
      (presentationStalkVariable B E α x)) := by
  let := algebraStalk a.hom x
  intro b
  obtain ⟨p, hp⟩ := stalkMap_surjective
    (presentation (Opens.grothendieckTopology T) A B a E α).hom x b
  exact ⟨freeAlgebraSheafStalkRingEquiv A E x p,
    (stalkFunctor_map_presentation_apply A B a E α x p).symm.trans hp⟩

/-- The family of generators `Eₓ → Bₓ` of `Bₓ` over `Aₓ` given by the germs of the generators
`α`. -/
abbrev presentationStalkGenerators :
    letI := algebraStalk a.hom x
    Algebra.Generators (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) (E.stalk x) :=
  letI := algebraStalk a.hom x
  Algebra.Generators.ofSurjective _ (aeval_presentationStalkVariable_surjective A B a E α x)

/-- The extension of `Bₓ` over `Aₓ` given by the stalk of the presentation `A[E] ⟶ B`. -/
abbrev presentationStalkExtension :
    letI := algebraStalk a.hom x
    Algebra.Extension.{u} (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) :=
  stalkExtension A (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
    (presentation (Opens.grothendieckTopology T) A B a E α) a x
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology T) A B E a α)

/-- **The stalk of the presentation is the presentation by the germs of the generators**, as a
morphism of extensions whose underlying ring homomorphism is `(A[E])ₓ ≅ Aₓ[Eₓ]`. -/
def presentationStalkExtensionHom :
    letI := algebraStalk a.hom x
    (presentationStalkExtension A B a E α x).Hom
      (presentationStalkGenerators A B a E α x).toExtension :=
  letI := algebraStalk a.hom x
  { toRingHom := (freeAlgebraSheafStalkRingEquiv A E x).toRingHom
    toRingHom_algebraMap := fun r =>
      (freeAlgebraSheafStalkRingEquiv_coefficientMap A E x r).trans
        (DFunLike.congr_fun (MvPolynomial.algebraMap_eq
          (R := ToType (TopCat.Presheaf.stalk A.obj x)) (σ := E.stalk x)).symm r)
    algebraMap_toRingHom := fun p =>
      (stalkFunctor_map_presentation_apply A B a E α x p).symm }

/-- The morphism of extensions in the other direction, with underlying ring homomorphism
`Aₓ[Eₓ] ≅ (A[E])ₓ`. -/
def presentationStalkExtensionInvHom :
    letI := algebraStalk a.hom x
    (presentationStalkGenerators A B a E α x).toExtension.Hom
      (presentationStalkExtension A B a E α x) :=
  letI := algebraStalk a.hom x
  { toRingHom := (freeAlgebraSheafStalkRingEquiv A E x).symm.toRingHom
    toRingHom_algebraMap := fun r =>
      (RingEquiv.symm_apply_eq _).mpr
        ((presentationStalkExtensionHom A B a E α x).toRingHom_algebraMap r).symm
    algebraMap_toRingHom := fun q =>
      ((congrArg (algebraMap (presentationStalkGenerators A B a E α x).toExtension.Ring
            (ToType (TopCat.Presheaf.stalk B.obj x)))
          ((freeAlgebraSheafStalkRingEquiv A E x).apply_symm_apply q)).symm.trans
        ((presentationStalkExtensionHom A B a E α x).algebraMap_toRingHom
          ((freeAlgebraSheafStalkRingEquiv A E x).symm q))).symm }

/-- If `g ∘ f` is the identity morphism of extensions, then `g` undoes `f` on cotangent spaces. -/
private theorem map_map_of_comp_eq_id {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Algebra.Extension R S} (f : P.Hom Q) (g : Q.Hom P)
    (h : g.comp f = Algebra.Extension.Hom.id P) (z : P.CotangentSpace) :
    Algebra.Extension.CotangentSpace.map g (Algebra.Extension.CotangentSpace.map f z) = z := by
  rw [← Algebra.Extension.CotangentSpace.map_comp_apply, h,
    Algebra.Extension.CotangentSpace.map_id]
  rfl

/-- **The cotangent spaces of the two presentations of `Bₓ` agree.** -/
theorem bijective_cotangentSpaceMap_presentationStalkExtensionHom :
    letI := algebraStalk a.hom x
    Function.Bijective
      (Algebra.Extension.CotangentSpace.map (presentationStalkExtensionHom A B a E α x)) := by
  let := algebraStalk a.hom x
  have h₁ : (presentationStalkExtensionInvHom A B a E α x).comp
      (presentationStalkExtensionHom A B a E α x) =
        Algebra.Extension.Hom.id (presentationStalkExtension A B a E α x) :=
    Algebra.Extension.Hom.ext (RingHom.ext fun p =>
      (freeAlgebraSheafStalkRingEquiv A E x).symm_apply_apply p)
  have h₂ : (presentationStalkExtensionHom A B a E α x).comp
      (presentationStalkExtensionInvHom A B a E α x) =
        Algebra.Extension.Hom.id (presentationStalkGenerators A B a E α x).toExtension :=
    Algebra.Extension.Hom.ext (RingHom.ext fun q =>
      (freeAlgebraSheafStalkRingEquiv A E x).apply_symm_apply q)
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Algebra.Extension.CotangentSpace.map (presentationStalkExtensionInvHom A B a E α x),
      fun z => ?_, fun z => ?_⟩
  · exact map_map_of_comp_eq_id _ _ h₁ z
  · exact map_map_of_comp_eq_id _ _ h₂ z

/-- The degree `0` term of `NL(α)` is the tensor-differentials sheaf of the presentation. -/
theorem presentationNaiveCotangentComplex_X_zero_eq_tensorDifferentialsSheaf :
    (presentationNaiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a E
        α).X 0 =
      tensorDifferentialsSheaf (Opens.grothendieckTopology T) A
        (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
        (presentation (Opens.grothendieckTopology T) A B a E α) :=
  presentationNaiveCotangentComplex_X_zero.{u, u, u, u} (Opens.grothendieckTopology T) A B a E α

/-- The cotangent space of the generators `Eₓ → Bₓ`, as a module over the `RingCat`-valued
stalk of the sheaf of rings underlying `B`, along `SemilinearStalk.commStalkRingEquiv`. -/
@[instance_reducible]
def moduleRingStalkPresentationCotangentSpace :
    letI := algebraStalk a.hom x
    Module (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
      (presentationStalkGenerators A B a E α x).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom x
  Module.compHom _ (SemilinearStalk.commStalkRingEquiv B.obj x).toRingHom

/-- The stalk of the tensor-differentials sheaf of the presentation is
`Bₓ ⊗_{(A[E])ₓ} Ω[(A[E])ₓ/Aₓ]`, the cotangent space of the stalk of the presentation
(`Stacks.Sites.Conormal.cotangentSpaceStalkLinearEquiv`), as an additive equivalence. -/
def presentationTensorStalkTensorEquiv :=
  letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
      (presentation (Opens.grothendieckTopology T) A B a E α) x).toAddEquiv

/-- **The stalk of the tensor-differentials sheaf of the presentation is the cotangent space of
the generators `Eₓ → Bₓ`**, as an additive equivalence: the cotangent space of the stalk of the
presentation is identified with that of the generators by the morphism of extensions
`presentationStalkExtensionHom`. -/
def presentationTensorStalkCotangentSpaceEquiv :=
  letI := algebraStalk a.hom x
  (presentationTensorStalkTensorEquiv A B a E α x).trans (AddEquiv.ofBijective
    (Algebra.Extension.CotangentSpace.map
      (presentationStalkExtensionHom A B a E α x)).toAddMonoidHom
    (bijective_cotangentSpaceMap_presentationStalkExtensionHom A B a E α x))

/-- **The identification of the stalk of the tensor-differentials sheaf with the cotangent space
of the generators is linear** over the stalk of the sheaf of rings underlying `B`.  A scalar `s`
is the image of a section `r` of the stalk of `A[E]`, since the presentation is surjective on
stalks; on the stalk of the tensor-differentials sheaf `s` acts as `r`, the identification of
`cotangentSpaceStalkLinearEquiv` is `(A[E])ₓ`-linear, and the map of cotangent spaces is
`Bₓ`-linear. -/
theorem presentationTensorStalkCotangentSpaceEquiv_smul
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology T) A
        (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
        (presentation (Opens.grothendieckTopology T) A B a E α)).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI := moduleRingStalkPresentationCotangentSpace A B a E α x
    presentationTensorStalkCotangentSpaceEquiv A B a E α x (s • ξ) =
      s • presentationTensorStalkCotangentSpaceEquiv A B a E α x ξ := by
  let := algebraStalk a.hom x
  let := moduleRingStalkPresentationCotangentSpace A B a E α x
  let := algebraStalk (presentation (Opens.grothendieckTopology T) A B a E α).hom x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  obtain ⟨r₀, hr⟩ := stalkMap_surjective
    (presentation (Opens.grothendieckTopology T) A B a E α).hom
    x (SemilinearStalk.commStalkRingEquiv B.obj x s)
  let r : ToType (TopCat.Presheaf.stalk
    (freeAlgebraSheaf (Opens.grothendieckTopology T) A E).obj x) := r₀
  have hs : (SemilinearStalk.commStalkRingEquiv B.obj x).symm
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology T) A B a E α).hom).hom r) = s :=
    Eq.trans (congrArg (SemilinearStalk.commStalkRingEquiv B.obj x).symm hr)
      ((SemilinearStalk.commStalkRingEquiv B.obj x).symm_apply_apply s)
  have h2 := tensorDifferentialsSheafStalk_ringCat_smul_eq A
      (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
      (presentation (Opens.grothendieckTopology T) A B a E α) x r ξ
  rw [hs] at h2
  have h3 := map_smul (cotangentSpaceStalkLinearEquiv A
      (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
      (presentation (Opens.grothendieckTopology T) A B a E α) x) r ξ
  have h4 := algebraMap_smul (ToType (TopCat.Presheaf.stalk B.obj x)) r
      (presentationTensorStalkTensorEquiv A B a E α x ξ)
  have h5 := map_smul (Algebra.Extension.CotangentSpace.map
      (presentationStalkExtensionHom A B a E α x))
    (algebraMap (ToType (TopCat.Presheaf.stalk
      (freeAlgebraSheaf (Opens.grothendieckTopology T) A E).obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) r)
      (presentationTensorStalkTensorEquiv A B a E α x ξ)
  exact (congrArg (Algebra.Extension.CotangentSpace.map
      (presentationStalkExtensionHom A B a E α x))
    ((congrArg (presentationTensorStalkTensorEquiv A B a E α x) h2.symm).trans
        (h3.trans h4.symm))).trans (h5.trans
      (congrArg (fun c : ToType (TopCat.Presheaf.stalk B.obj x) => c •
        Algebra.Extension.CotangentSpace.map (presentationStalkExtensionHom A B a E α x)
          (presentationTensorStalkTensorEquiv A B a E α x ξ)) hr))

/-- **The stalk of the tensor-differentials sheaf of the presentation is the cotangent space of
the generators `Eₓ → Bₓ`, as modules over the stalk of `B`.** -/
def presentationTensorStalkCotangentSpaceLinearEquiv :=
  letI := algebraStalk a.hom x
  letI := moduleRingStalkPresentationCotangentSpace A B a E α x
  (presentationTensorStalkCotangentSpaceEquiv A B a E α x).toLinearEquiv
    (R := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x))
    (presentationTensorStalkCotangentSpaceEquiv_smul A B a E α x)

/-- **The tensor-differentials sheaf `B ⊗_{A[E]} Ω_{A[E]/A}` of a presentation is a flat
`B`-module.** -/
theorem isFlat_presentationTensorDifferentialsSheaf :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (tensorDifferentialsSheaf (Opens.grothendieckTopology T) A
        (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
        (presentation (Opens.grothendieckTopology T) A B a E α)) := by
  refine (isFlat_iff_stalk_flat B _).2 fun x => ?_
  let : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) B.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T)
        (tensorDifferentialsSheaf (Opens.grothendieckTopology T) A
          (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
          (presentation (Opens.grothendieckTopology T) A B a E α)).val.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := T) B.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := T)
        ((id (tensorDifferentialsSheaf (Opens.grothendieckTopology T) A
          (freeAlgebraSheaf (Opens.grothendieckTopology T) A E) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology T) A E)
          (presentation (Opens.grothendieckTopology T) A B a E α)).val :
            _root_.PresheafOfModules.{u}
              (B.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
  let := algebraStalk a.hom x
  let := moduleRingStalkPresentationCotangentSpace A B a E α x
  let e : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj x) ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) B.obj x) :=
    SemilinearStalk.commStalkRingEquiv B.obj x
  have hsmul : ∀ (c : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) B.obj x))
      (y : (presentationStalkGenerators A B a E α x).toExtension.CotangentSpace),
      e.symm c • y = c • y := by
    intro c y
    show e (e.symm c) • y = c • y
    rw [e.apply_symm_apply]
  exact @Module.Flat.of_free _ _ _ _ _
    (Module.Free.of_basis
      ((((presentationStalkGenerators A B a E α x).cotangentSpaceBasis.mapCoeffs
          e.symm hsmul).map
            (presentationTensorStalkCotangentSpaceLinearEquiv A B a E α x).symm).mapCoeffs
            e (commStalkRingEquiv_smul_eq' B x _)))

/-- **The degree `0` term of the naive cotangent complex of a presentation is a flat
`B`-module.**  It is the tensor-differentials sheaf `B ⊗_{A[E]} Ω_{A[E]/A}` of the presentation;
flatness is stalkwise (Stacks 05NE), and the stalk at `x` is the cotangent space of the
generators `Eₓ → Bₓ` of `Bₓ` over `Aₓ`
(`Stacks.SheafOfModules.presentationTensorStalkCotangentSpaceLinearEquiv`), which is free on `Eₓ`
by `Algebra.Generators.cotangentSpaceBasis`. -/
theorem isFlat_presentationNaiveCotangentComplex_X_zero :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      ((presentationNaiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a E
        α).X 0) := by
  rw [presentationNaiveCotangentComplex_X_zero_eq_tensorDifferentialsSheaf]
  exact isFlat_presentationTensorDifferentialsSheaf A B a E α

end Stacks.SheafOfModules

end

end
