module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivationKernelDescent
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex

/-!
# The derivations of the structure sheaf of a closed subspace, as derivations on the ambient space

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over `B` and `b : X ⟶ B` a structure
morphism.  This file identifies
```
  Der_B(𝒪_Z, W) ≃ {D ∈ Der_B(𝒪_X, i_*W) : D kills the kernel of i♯}
```
for every `𝒪_Z`-module `W`, where `i♯ : 𝒪_X ⟶ i_*𝒪_Z` is the direct-image form of the structure
map of Stacks 03G8.

**This is the unwinding of exactness at the middle term of Stacks 05ZA.**  Through Equation
(0619) a morphism `i^*Ω_{X/B} ⟶ W` out of the middle term of the conormal sequence is a
`B`-derivation of `𝒪_X` with values in `i_*W`; it annihilates the first arrow exactly when that
derivation kills the defining ideal sheaf of `Z`
(`AlgebraicGeometry.Space.derivationDirectImageEquiv_d_eq_zero`), and the defining ideal sheaf
*is* the kernel of `i♯` (`AlgebraicGeometry.Space.mem_definingIdealAt_iff`).  So the bijection
below is exactly the statement that the second arrow of the conormal sequence is a cokernel of
the first, read through the universal property of `Ω_{Z/B}`.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_structureSharpCommRing`: the structure map of a
  closed immersion is locally surjective as a map of sheaves of *commutative* rings.  This is
  Stacks 03MB, carried across `forget₂ CommRingCat RingCat`.
* `AlgebraicGeometry.Space.directImageCoefficientIso`: **the coefficient identification.**  The
  direct image `i_*W` of Stacks 03D1 over `i_*𝒪_Z` is the coefficient module that the
  transposition of Stacks 08TQ produces, namely the direct image over `i⁻¹i_*𝒪_Z` of `W` with its
  scalars restricted along the counit.
* `AlgebraicGeometry.Space.directImageDerivationKernelEquiv`: the bijection
  `Der_B(𝒪_Z, W) ≃ {D ∈ Der_B(𝒪_X, i_*W) : D|ker i♯ = 0}`.

## Implementation notes

**Why the descent runs on the site of `X` and not on the site of `Z`.**  The descent of
derivations along a locally surjective homomorphism of sheaves of rings
(`Stacks.Sites.Conormal.derivationKernelEquiv`) asks that the derivation kill the *kernel* of
that homomorphism.  Along the direct-image form `i♯ : 𝒪_X ⟶ i_*𝒪_Z` on the site of `X` that
kernel *is* the defining ideal sheaf, by
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`.  So the hypothesis the conormal sequence
supplies is literally the hypothesis the descent consumes, and no ideal comparison intervenes.

**Along the inverse-image form the identification is exactness, not generation.**  Along
`i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` on the site of `Z` the kernel is not the inverse image of the defining ideal
sheaf on the nose, and identifying the two is *exactness of the inverse image of sheaves of
modules* — **no generation statement is involved**.
`AlgebraicGeometry.Space.isLimit_kernelFork_directImageDefiningIdeal` in
`StacksFrontier/AlgebraicGeometry/Spaces/InverseImageDefiningIdealKernel.lean` exhibits
`i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X` as a kernel of `i_*i⁻¹(i♯ : 𝒪_X ⟶ i_*𝒪_Z)`, out of the short exact
sequence `0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` of Stacks 03MB
(`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`) and
`Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules`, and reads it on sections.
The *inverse-image* form differs from `i⁻¹(i♯)` only by the counit `i⁻¹i_*𝒪_Z ⟶ 𝒪_Z`
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`), which is invertible for a closed
immersion (`AlgebraicGeometry.Space.isIso_commRingCounit_of_isClosedImmersion`), so the two have
the same kernel; what is *not* yet proved is that identification read on sections.  The route of
this file is the shorter one.

**The coefficient identification is the triangle identity.**  The transposition of Stacks 08TQ
(`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`) states its coefficient as
`directImageModules`, which is the direct image over `i⁻¹i_*𝒪_Z` followed by restriction of
scalars along the unit `i_*𝒪_Z ⟶ i_*i⁻¹i_*𝒪_Z`; what the conormal sequence hands over is the
direct image over `𝒪_Z` itself.  The two have the same underlying sheaf of sets, and the scalar
actions agree because
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso` moves the restriction
along the counit through the direct image and the composite
`i_*𝒪_Z ⟶ i_*i⁻¹i_*𝒪_Z ⟶ i_*𝒪_Z` of the unit with the direct image of the counit is the
identity — the triangle identity of
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, read at the commutative-ring counit
through `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forgetCommRing`.

Note that `Stacks.Sheaves.RingedToposModules.directImageModulesRestrictScalarsIso` does *not* do
this: it moves a restriction of scalars along a map of the *target* site's rings through the
direct image, whereas the counit is a map of the source site's rings and is not an inverse image.

**What makes the whole chain cheap** is that the three spellings of the direct image of modules
agree definitionally at these sites: `AlgebraicGeometry.Space.moduleDirectImage` is
`Stacks.Sheaves.RingedToposModules.pushforwardModuleFunctor` of the morphism of ringed topoi, and
`AlgebraicGeometry.Space.modulePushforward` is that followed by restriction of scalars along the
structure map, by `AlgebraicGeometry.Space.modulePushforward_eq`.  The one step that is *not*
definitional is replacing the commutative-ring structure map by the ring-valued one, because
`AlgebraicGeometry.Space.structureSharpCommRing` is irreducible; that is
`AlgebraicGeometry.Space.map_structureSharpCommRing`, used once.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence,
  for whose exactness at the middle term this is the derivation-level content.
* [Stacks Project, Tag 08TF](https://stacks.math.columbia.edu/tag/08TF), the conormal sequence of
  a surjection of sheaves of rings, whose middle exactness the descent is.
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ), the transposition of
  derivations along an inverse image.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), surjectivity of the
  structure map of a closed immersion and the defining ideal sheaf as its kernel.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), which makes
  the counit invertible.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z X Bb : AlgebraicSpaces B S hS}

/-- **Stacks 03MB for sheaves of commutative rings.**  The structure map
`i♯ : 𝒪_X ⟶ i_*𝒪_Z` of a closed immersion is locally surjective as a homomorphism of sheaves of
commutative rings on the small étale site of `X`.

Local surjectivity is a property of the underlying morphism of sheaves of sets, and
`AlgebraicGeometry.Space.map_structureSharpCommRing` identifies that morphism with the one of
`AlgebraicGeometry.Space.structureSharp`, which is locally surjective by
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`. -/
theorem isLocallySurjective_structureSharpCommRing (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharpCommRing B S hS i).hom := by
  have h := isLocallySurjective_structureSharp B S hS i hi
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  show Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      ((Stacks.forgetCommRingSheaf.{u, u + 1, u}
          (SmallEtale.topology B S hS X.1)).map (structureSharpCommRing B S hS i))).hom
  rw [map_structureSharpCommRing]
  exact (Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 h

/-- The direct image `i_*𝒪_Z` of the structure sheaf of `Z`, read as a sheaf of rings on the
small étale site of `X`.  This is the sheaf of rings the descent of derivations runs over, and it
is `AlgebraicGeometry.Space.structureRingSheafDirectImage` definitionally. -/
noncomputable abbrev directImageStructureRingSheaf (i : Z ⟶ X) :=
  Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallToposMorphismTypeU B S hS i)).obj
      (smallEtaleRingedTopos B S hS Z).O)

/-- The direct image of an `𝒪_Z`-module over `i_*𝒪_Z`, read at the spelling
`AlgebraicGeometry.Space.directImageStructureRingSheaf` of that sheaf of rings.  The two
spellings are definitionally equal; this names the one the descent's statement elaborates
against, so that nothing has to infer it from the other. -/
noncomputable abbrev directImageModuleOver (i : Z ⟶ X) (W : Modules.{u, u} B S hS Z.1 Z.2) :
    _root_.SheafOfModules.{u} (directImageStructureRingSheaf B S hS i) :=
  (moduleDirectImage B S hS i).obj W

/-- The commutative-ring counit `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` of a closed immersion, read as a homomorphism
of sheaves of rings.  Restriction of scalars along it is
`AlgebraicGeometry.Space.counitRestrictScalars`. -/
noncomputable abbrev counitRingMap (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    inverseImageRingSheaf (smallEtaleRingedToposHom B S hS i).toToposHom
        (directImageStructureRingSheaf B S hS i) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS Z).O :=
  (Stacks.forgetCommRingSheaf.{u, u + 1, u} (SmallEtale.topology B S hS Z.1)).map
    (structureCounitIso B S hS i hi).hom

/-- **The triangle identity at the structure sheaf of `Z`.**  The unit
`i_*𝒪_Z ⟶ i_*i⁻¹i_*𝒪_Z` followed by the direct image of the counit `i⁻¹i_*𝒪_Z ⟶ 𝒪_Z` is the
identity of `i_*𝒪_Z`.

This is `CategoryTheory.Adjunction.right_triangle_components` for
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, with the commutative-ring counit
identified with the ring counit by
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction_counit_forgetCommRing`. -/
theorem ringUnit_comp_pushforward_counitRingMap (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    ringUnit (smallEtaleRingedToposHom B S hS i).toToposHom
          (directImageStructureRingSheaf B S hS i) ≫
        pushforwardRingMap (smallEtaleRingedToposHom B S hS i).toToposHom
          (counitRingMap B S hS i hi) =
      𝟙 (directImageStructureRingSheaf B S hS i) := by
  have h := (ringImageAdjunction (smallEtaleRingedToposHom B S hS i).toToposHom
    ).right_triangle_components
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O)
  refine Eq.trans ?_ h
  exact congrArg (fun m ↦ ringUnit (smallEtaleRingedToposHom B S hS i).toToposHom
      (directImageStructureRingSheaf B S hS i) ≫ pushforwardRingMap _ m)
    (commRingImageAdjunction_counit_forgetCommRing
      (smallEtaleRingedToposHom B S hS i).toToposHom (smallEtaleRingedTopos B S hS Z).O)

/-- **The coefficient identification.**  For a closed immersion `i : Z ⟶ X` and an `𝒪_Z`-module
`W`, the direct image of `W` over `i_*𝒪_Z` of Stacks 03D1 is the coefficient module the
transposition of Stacks 08TQ produces: the direct image over `i⁻¹i_*𝒪_Z` of `W` with its scalars
restricted along the counit, read back over `i_*𝒪_Z` along the unit.

The two have the same underlying sheaf of sets; what the isomorphism does is identify the scalar
actions, and that is the triangle identity
`AlgebraicGeometry.Space.ringUnit_comp_pushforward_counitRingMap` together with
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, which moves a
restriction of scalars on the source through the direct image. -/
noncomputable def directImageCoefficientIso (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (W : Modules.{u, u} B S hS Z.1 Z.2) :
    (moduleDirectImage B S hS i).obj W ≅
      (directImageModules (smallEtaleRingedToposHom B S hS i).toToposHom
        (directImageStructureRingSheaf B S hS i)).obj
          (counitRestrictScalars B S hS i hi W) :=
  eqToIso (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj
      ((moduleDirectImage B S hS i).obj W))
    (ringUnit_comp_pushforward_counitRingMap B S hS i hi).symm) ≪≫
    (SheafOfModules.restrictScalars
      (ringUnit (smallEtaleRingedToposHom B S hS i).toToposHom
        (directImageStructureRingSheaf B S hS i))).mapIso
      (pullbackModuleObjRestrictScalarsIso (SmallEtale.topology B S hS X.1)
        (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward
        (counitRingMap B S hS i hi) W)

/-- The coefficient of the descent of derivations along `i♯ : 𝒪_X ⟶ i_*𝒪_Z` is the direct image
`i_*W` of Stacks 03LU.

Everything here is definitional except the replacement of
`AlgebraicGeometry.Space.structureSharpCommRing` by
`AlgebraicGeometry.Space.structureSharp`, which is
`AlgebraicGeometry.Space.map_structureSharpCommRing`. -/
theorem restrictModuleAlong_moduleDirectImage (i : Z ⟶ X)
    (W : Modules.{u, u} B S hS Z.1 Z.2) :
    Stacks.Sites.Conormal.restrictModuleAlong (SmallEtale.topology B S hS X.1)
        (directImageModuleOver B S hS i W) (structureSharpCommRing B S hS i).hom =
      ((modulePushforward B S hS i).obj W).val :=
  congrArg (fun m ↦ ((SheafOfModules.restrictScalars m).obj
    (directImageModuleOver B S hS i W)).val) (map_structureSharpCommRing B S hS i)

/-! ### Transport along an equality of the coefficient -/

section Transport

universe t₀ w₀ v₀ u₀

variable {E : Type u₀} [Category.{v₀} E] {S₀ R₀ : Eᵒᵖ ⥤ CommRingCat.{w₀}} {φ : S₀ ⟶ R₀}
  {A : Type t₀}
  {P : ∀ _K : PresheafOfModules.{w₀} (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀}),
    _K.Derivation' φ → Prop}

/-- **Transport, along an equality of the coefficient presheaf of modules, of a bijection onto
the derivations satisfying a condition.**

This is `h ▸ e`, named rather than written inline so that
`AlgebraicGeometry.Space.derivationSubtypeTransport_coe_d` can describe its values.  The cast
that description leaves behind is between the sections of two presheaves of modules which differ
only in their scalar action, so at a concrete transport it disappears by `rfl`. -/
noncomputable def derivationSubtypeTransport
    {M N : PresheafOfModules.{w₀} (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀})} (h : M = N)
    (e : A ≃ {D : M.Derivation' φ // P M D}) : A ≃ {D : N.Derivation' φ // P N D} :=
  h ▸ e

/-- **The transport of `AlgebraicGeometry.Space.derivationSubtypeTransport` acts on the value of
a derivation on a local section by a cast**, the cast being the one the equality of the
coefficients induces on sections. -/
theorem derivationSubtypeTransport_coe_d
    {M N : PresheafOfModules.{w₀} (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀})} (h : M = N)
    (e : A ≃ {D : M.Derivation' φ // P M D}) (x : A) (Y : Eᵒᵖ) (y : ToType (R₀.obj Y)) :
    ((derivationSubtypeTransport (P := P) h e x).1).d y =
      cast (congrArg (fun K : PresheafOfModules.{w₀}
          (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀}) ↦ ToType (K.obj Y)) h)
        (((e x).1).d y) := by
  cases h
  rfl

end Transport

/-- **`Der_B(𝒪_Z, W) ≃ {D ∈ Der_B(𝒪_X, i_*W) : D kills ker i♯}` for a closed immersion.**  A
`B`-derivation of `𝒪_X` with values in the direct image `i_*W` which annihilates every local
section killed by the structure map `i♯ : 𝒪_X ⟶ i_*𝒪_Z` comes from a unique `B`-derivation of
`𝒪_Z` with values in `W`, and conversely.

The sections `i♯` kills are exactly the sections of the defining ideal sheaf of `Z`, by
`AlgebraicGeometry.Space.mem_definingIdealAt_iff`, so this is the descent the exactness of the
conormal sequence of Stacks 05ZA at its middle term needs.

Three bijections of the library composed: the descent of derivations along a locally surjective
homomorphism of sheaves of rings
(`Stacks.Sites.Conormal.derivationKernelEquiv`, whose coefficient universe is free, with its
hypothesis discharged by
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpCommRing`), the coefficient
identification `AlgebraicGeometry.Space.directImageCoefficientIso`, and the transport
`AlgebraicGeometry.Space.directImageDerivationEquiv` of a derivation of `i_*𝒪_Z` into a direct
image to a derivation of `𝒪_Z`. -/
noncomputable def directImageDerivationKernelEquiv (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Z.1 Z.2) :
    W.val.Derivation' ((smallEtaleRingedToposHom B S hS (i ≫ b)).fSharpInverseImage).hom ≃
      {D : ((modulePushforward B S hS i).obj W).val.Derivation'
            (structureSharpInverseImage B S hS b).hom //
        ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
          (x : ToType ((structureRingSheaf B S hS X).obj.obj U)),
          ((structureSharpCommRing B S hS i).hom.app U) x = 0 → D.d x = 0} := by
  haveI := isLocallySurjective_structureSharpCommRing B S hS i hi
  haveI : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  exact derivationSubtypeTransport
    (P := fun _ D ↦ ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (x : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      ((structureSharpCommRing B S hS i).hom.app U) x = 0 → D.d x = 0)
    (restrictModuleAlong_moduleDirectImage B S hS i W)
    ((directImageDerivationEquiv B S hS i hi b W).symm.trans
      ((PresheafOfModules.Derivation.postcompEquiv
          ((_root_.SheafOfModules.forget _).mapIso
            (directImageCoefficientIso B S hS i hi W).symm)).trans
        (Stacks.Sites.Conormal.derivationKernelEquiv (SmallEtale.topology B S hS X.1)
          (structureSharpInverseImage B S hS b).hom (structureSharpCommRing B S hS i)
          (directImageModuleOver B S hS i W))))

/-- **The descent of `AlgebraicGeometry.Space.directImageDerivationKernelEquiv` on a local
section.**  The `B`-derivation of `𝒪_X` that the descent attaches to a `B`-derivation `D` of
`𝒪_Z` carries a local section `t` of `𝒪_X` to the value at `i♯ t` of the transposition of `D`
across `i^{-1} ⊣ i_*`.

This is `Stacks.Sites.Conormal.restrictDerivation_d` — the forward direction of the descent is
precomposition with `i♯` on sections — together with
`AlgebraicGeometry.Space.derivationSubtypeTransport_coe_d`, whose cast disappears because the
two coefficient presheaves differ only in their scalar action. -/
theorem directImageDerivationKernelEquiv_coe_d (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (b : X ⟶ Bb)
    (W : Modules.{u, u} B S hS Z.1 Z.2)
    (D : W.val.Derivation' ((smallEtaleRingedToposHom B S hS (i ≫ b)).fSharpInverseImage).hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS X).obj.obj U)) :
    ((directImageDerivationKernelEquiv B S hS i hi b W D).1).d t =
      (PresheafOfModules.Derivation.postcompEquiv
          ((_root_.SheafOfModules.forget _).mapIso
            (directImageCoefficientIso B S hS i hi W).symm)
        ((directImageDerivationEquiv B S hS i hi b W).symm D)).d
        (((structureSharpCommRing B S hS i).hom.app U) t) := by
  have := isLocallySurjective_structureSharpCommRing B S hS i hi
  have : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  exact derivationSubtypeTransport_coe_d _ _ D U t

end AlgebraicGeometry.Space

end
