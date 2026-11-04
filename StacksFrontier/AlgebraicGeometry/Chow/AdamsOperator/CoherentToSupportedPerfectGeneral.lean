module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentToSupportedPerfect

/-!
# From coherent sheaves on a closed subscheme to perfect complexes, for any derived category

`StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentToSupportedPerfect` constructs, for a
closed immersion `i : Z ⟶ X` with `X` regular, the canonical homomorphism
`K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))` of [Stacks, Tag 0FEQ], with the derived category of
`𝒪_X`-modules read at `CategoryTheory.HasDerivedCategory.standard`. This module constructs the
same homomorphism for an arbitrary model `[HasDerivedCategory.{w} (OXMod X.toRingedSpace)]` of
the derived category, in any universe `w`, so that it can be composed with constructions read at
another model (the localized Chern character of Remark 42.56.11 is read at a model with morphisms
in `Type (u + 1)`).

## Main definitions

* `AlgebraicGeometry.singlePushforwardSupportedPerfectGeneral` is the object `(i_*ℱ)[0]` of
  `D_{Z, perf}(𝒪_X)` attached to a coherent `𝒪_Z`-module `ℱ`.
* `AlgebraicGeometry.coherentToSupportedPerfectHomGeneral` is the canonical homomorphism
  `K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))`.

## Main results

* `AlgebraicGeometry.coherentToSupportedPerfectHomGeneral_mk` computes the homomorphism on the
  class of a coherent `𝒪_Z`-module: it is the class of `(i_*ℱ)[0]`.
* `AlgebraicGeometry.cls_singlePushforwardSupportedPerfectGeneral_add` is the additivity along a
  short exact sequence of coherent modules which makes the homomorphism well defined.

## References

* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe w v u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsRegular X)

/-- **A coherent module on a closed subscheme of a regular scheme, pushed forward and placed in
degree zero, is a perfect complex supported on that subscheme.** The direct image `i_*ℱ` of a
coherent `𝒪_Z`-module `ℱ` is coherent by [Stacks, Tag 087T], hence `(i_*ℱ)[0]` is a perfect
object of `D(𝒪_X)` by the degree-zero case of [Stacks, Tag 0FDC]; its cohomology sheaf in degree
zero is `i_*ℱ`, whose stalks vanish off the image of `i`, and its cohomology sheaves in all
other degrees vanish. -/
def singlePushforwardSupportedPerfectGeneral
    [HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace)]
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    supportedPerfectDerivedCategory i :=
  ⟨(DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
      ((Scheme.Modules.pushforward i).obj F.obj),
    have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    have : SheafOfModules.IsCoherent (F.obj : Z.Modules) :=
      CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    have : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj F.obj) :=
      isCoherent_pushforward_of_isClosedImmersion i (F.obj : Z.Modules)
    isPerfect_single_of_isCoherent_of_isRegular hX _, by
    intro n
    by_cases hn : n = 0
    · subst hn
      refine (SheafOfModules.supp_eq_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (OXMod.{u, u} X.toRingedSpace) 0).app
          ((Scheme.Modules.pushforward i).obj F.obj))).subset.trans ?_
      intro x hx
      by_contra hxr
      exact notMem_supp_pushforward_of_notMemRange i (F.obj : Z.Modules) x hxr hx
    · have hz := DerivedCategory.isZero_homology_singleFunctor_obj
        (C := OXMod.{u, u} X.toRingedSpace) ((Scheme.Modules.pushforward i).obj F.obj) hn
      have h0 : SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
              ((Scheme.Modules.pushforward i).obj F.obj))) = ∅ :=
        SheafOfModules.supp_eq_empty_of_isZero hz
      exact h0.subset.trans (Set.empty_subset _)⟩

/-- The underlying object of `D(𝒪_X)` of `(i_*ℱ)[0]` is the direct image of `ℱ` placed in degree
zero. -/
@[simp]
theorem singlePushforwardSupportedPerfectGeneral_obj
    [HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace)]
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    (singlePushforwardSupportedPerfectGeneral i hX F).obj =
      (DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
        ((Scheme.Modules.pushforward i).obj F.obj) :=
  rfl

/-- **The class of `(i_*ℱ)[0]` is additive along short exact sequences of coherent modules.** The
functor taking a coherent `𝒪_Z`-module to its direct image is exact, being the composite of the
exact inclusion of coherent modules into all `𝒪_Z`-modules ([Stacks, Tag 01BY]) with the exact
direct image along a closed immersion ([Stacks, Tag 08KS]), so a short exact sequence of coherent
`𝒪_Z`-modules gives a short exact sequence of `𝒪_X`-modules and hence a distinguished triangle of
the three direct images placed in degree zero. -/
theorem cls_singlePushforwardSupportedPerfectGeneral_add
    [HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace)]
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf))
    (hS : S.ShortExact) :
    Pretriangulated.K0.cls (singlePushforwardSupportedPerfectGeneral i hX S.X₂) =
      Pretriangulated.K0.cls (singlePushforwardSupportedPerfectGeneral i hX S.X₁) +
        Pretriangulated.K0.cls (singlePushforwardSupportedPerfectGeneral i hX S.X₃) := by
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} i.toRingCatSheafHom) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward i))
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} i.toRingCatSheafHom) :=
    Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion i
  have : (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).PreservesZeroMorphisms :=
    inferInstanceAs ((Scheme.Modules.pushforward i).PreservesZeroMorphisms)
  have : (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_full _
  have hS₁ : (S.map (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf))).ShortExact := hS.map_of_exact _
  have hS₂ : ((S.map (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf))).map
        (SheafOfModules.pushforward.{u} i.toRingCatSheafHom)).ShortExact := hS₁.map_of_exact _
  exact Pretriangulated.K0.cls_add_of_shortExact (C := OXMod.{u, u} X.toRingedSpace) hS₂
    (singlePushforwardSupportedPerfectGeneral i hX S.X₁)
    (singlePushforwardSupportedPerfectGeneral i hX S.X₂)
    (singlePushforwardSupportedPerfectGeneral i hX S.X₃) rfl rfl rfl

/-- **Stacks Project, Tag 0FEQ.** Let `i : Z ⟶ X` be a closed immersion of schemes with `X`
regular. There is a canonical homomorphism `K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))` taking the class
of a coherent `𝒪_Z`-module `ℱ` to the class of its direct image placed in degree zero.

The source is the Grothendieck group of the abelian category of coherent `𝒪_Z`-modules and the
target is the `K`-group of the triangulated category of perfect complexes on `X` supported on the
closed subset underlying `Z`. The map is well defined because the direct image of a short exact
sequence of coherent modules is short exact, hence gives a distinguished triangle of the three
degree-zero complexes. -/
@[stacks 0FEQ]
def coherentToSupportedPerfectHomGeneral
    [HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace)] :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) →+
      Pretriangulated.K0 (supportedPerfectDerivedCategory i) :=
  KZero.lift (fun F => Pretriangulated.K0.cls (singlePushforwardSupportedPerfectGeneral i hX F))
    (cls_singlePushforwardSupportedPerfectGeneral_add i hX)

/-- **Stacks Project, Tag 0FEQ.** The canonical homomorphism
`K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))` takes the class of a coherent `𝒪_Z`-module `ℱ` to the class
of the perfect complex `(i_*ℱ)[0]`. -/
@[simp, stacks 0FEQ]
theorem coherentToSupportedPerfectHomGeneral_mk
    [HasDerivedCategory.{w} (OXMod.{u, u} X.toRingedSpace)]
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    coherentToSupportedPerfectHomGeneral i hX (KZero.mk _ F) =
      Pretriangulated.K0.cls (singlePushforwardSupportedPerfectGeneral i hX F) :=
  KZero.lift_mk _ _ _

end AlgebraicGeometry

end
