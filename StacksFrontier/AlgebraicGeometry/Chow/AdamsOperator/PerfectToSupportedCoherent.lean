module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentToSupportedPerfect
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# From perfect complexes supported on a closed subscheme to coherent sheaves supported on it

Let `X` be a Noetherian regular scheme and `i : Z ⟶ X` a closed immersion. A perfect complex
`E` on `X` whose cohomology sheaves are supported on `Z` has coherent cohomology sheaves, only
finitely many of which are nonzero, so `E ↦ ∑ (-1)^n [H^n(E)]` is a well-defined element of
`K_0(Coh_Z(X))`, and taking cohomology is a homological functor `D_{Z, perf}(𝒪_X) ⥤ Coh_Z(X)`.
This gives the homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`. Composing it with the
homomorphism `K'_0(Z) = K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X))` which places a coherent
`𝒪_Z`-module in degree zero recovers the comparison homomorphism
`K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` of direct image.

## Main definitions

* `AlgebraicGeometry.supportedPerfectHomology` is the cohomology functor
  `D_{Z, perf}(𝒪_X) ⥤ Coh_Z(X)` in degree zero.
* `AlgebraicGeometry.supportedPerfectEulerHom` is the homomorphism
  `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`.

## Main results

* `AlgebraicGeometry.isHomological_supportedPerfectHomology`: taking cohomology in degree zero
  is a homological functor.
* `AlgebraicGeometry.finite_nonzero_supportedPerfectHomology`: for a fixed object only finitely
  many of its shifted cohomology sheaves are nonzero.
* `AlgebraicGeometry.supportedPerfectEulerHom_cls` computes the homomorphism on the class of an
  object: it is the alternating sum of the classes of the cohomology sheaves.
* `AlgebraicGeometry.supportedPerfectEulerHom_comp_coherentToSupportedPerfectHom`: the composite
  `K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` is the comparison homomorphism of
  direct image.

The value on a class is the alternating sum `∑_{n ∈ ℤ} (-1)^n [H^n(E)]`; its identification
with `[⊕_n H^{2n}(E)] - [⊕_n H^{2n+1}(E)]` is not proved here.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FER](https://stacks.math.columbia.edu/tag/0FER)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
  (hX : IsRegular X)

/-- The inclusion of a weak Serre subcategory reflects exactness of a short complex. -/
theorem exact_of_exact_map_ι {A : Type*} [Category A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] {S : ShortComplex P.FullSubcategory}
    (hS : (S.map P.ι).Exact) : S.Exact := by
  have : PreservesFiniteLimits P.ι := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  have : PreservesFiniteColimits P.ι := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have : P.ι.PreservesHomology := ⟨P.preservesKernels_ι, P.preservesCokernels_ι⟩
  exact (S.exact_map_iff_of_faithful P.ι).mp hS

/-- On a Noetherian regular scheme, the degree-zero cohomology of a perfect complex supported on a
closed subscheme, as a functor to coherent `𝒪_X`-modules. -/
def supportedPerfectHomologyCoherent :
    supportedPerfectDerivedCategory i ⥤ Stacks.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    (ObjectProperty.ι _ ⋙ DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0)
    fun E => CoherentAbelian.stacksIsCoherent_of_isCoherent
      ((Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
        X hX E.obj E.property.1).2 0)

/-- The degree-zero cohomology functor `D_{Z, perf}(𝒪_X) ⥤ Coh_Z(X)` on a Noetherian regular
scheme. -/
def supportedPerfectHomology :
    supportedPerfectDerivedCategory i ⥤ SupportedCoherentModules i :=
  ObjectProperty.lift (supportedCoherentProperty i) (supportedPerfectHomologyCoherent i hX)
    fun E => E.property.2 0

/-- The underlying `𝒪_X`-module of the degree-zero cohomology of `E` is `H^0(E)`. -/
@[simp]
theorem supportedPerfectHomology_obj (E : supportedPerfectDerivedCategory i) :
    ((supportedPerfectHomology i hX).obj E).obj.obj =
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj E.obj :=
  rfl

/-- The degree-zero cohomology functor `D_{Z, perf}(𝒪_X) ⥤ Coh_Z(X)` preserves zero morphisms. -/
instance preservesZeroMorphisms_supportedPerfectHomology :
    (supportedPerfectHomology i hX).PreservesZeroMorphisms where
  map_zero _ _ := (ObjectProperty.ι (supportedCoherentProperty i)).map_injective <|
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).map_injective <|
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).map_zero _ _

/-- The degree-zero cohomology functor `D_{Z, perf}(𝒪_X) ⥤ Coh_Z(X)` is homological. -/
instance isHomological_supportedPerfectHomology :
    (supportedPerfectHomology i hX).IsHomological where
  exact T hT := by
    refine exact_of_exact_map_ι (supportedCoherentProperty i) ?_
    refine exact_of_exact_map_ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) ?_
    exact Functor.map_distinguished_exact
      (ObjectProperty.ι _ ⋙ DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0) T hT

/-- A cohomology sheaf of a supported perfect complex which vanishes in the ambient category of
`𝒪_X`-modules is a zero object of `Coh_Z(X)`. -/
theorem isZero_supportedPerfectHomology_of_isZero (E : supportedPerfectDerivedCategory i)
    (n : ℤ)
    (hn : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E.obj)) :
    IsZero ((supportedPerfectHomology i hX).obj ((shiftFunctor (supportedPerfectDerivedCategory i)
      n).obj E)) := by
  refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι (supportedCoherentProperty i)) _ ?_
  refine IsZero.of_full_of_faithful_of_isZero
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)) _ ?_
  refine IsZero.of_iso hn ?_
  refine (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).mapIso
    ((Functor.commShiftIso (ObjectProperty.ι _) n).app E) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).shiftIso n 0 n
    (add_zero n)).app E.obj

/-- On a Noetherian regular scheme, only finitely many cohomology sheaves of a supported perfect
complex are nonzero. -/
theorem finite_nonzero_supportedPerfectHomology (E : supportedPerfectDerivedCategory i) :
    {n : ℤ | ¬ IsZero ((supportedPerfectHomology i hX).obj
      ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj E))}.Finite := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
      X hX E.obj E.property.1
  exact (Set.finite_Icc a b).subset fun n hn =>
    ⟨not_lt.1 fun h => hn (isZero_supportedPerfectHomology_of_isZero i hX E n (ha n h)),
      not_lt.1 fun h => hn (isZero_supportedPerfectHomology_of_isZero i hX E n (hb n h))⟩

/-- There is a homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` sending the class of `E` to
the alternating sum of the classes of its cohomology sheaves. -/
theorem exists_supportedPerfectEulerHom :
    ∃ φ : Pretriangulated.K0 (supportedPerfectDerivedCategory i) →+
      KZero (SupportedCoherentModules i),
      ∀ E : supportedPerfectDerivedCategory i, φ (Pretriangulated.K0.cls E) =
        eulerClass (supportedPerfectDerivedCategory i) (SupportedCoherentModules i)
          (supportedPerfectHomology i hX) E :=
  K0_homomorphism_of_homological (supportedPerfectDerivedCategory i)
    (SupportedCoherentModules i) (supportedPerfectHomology i hX)
    (isHomological_supportedPerfectHomology i hX) (finite_nonzero_supportedPerfectHomology i hX)

/-- The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`. Let `X` be a Noetherian regular
scheme and `Z ⊂ X` a closed subscheme. Taking the alternating sum of the cohomology sheaves of a
perfect complex supported on `Z` defines a homomorphism from the `K`-group of `D_{Z, perf}(𝒪_X)`
to the Grothendieck group of coherent `𝒪_X`-modules supported on `Z`. -/
@[stacks 0FEP "the homomorphism K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)). Two departures from the \
source, both recorded in the module docstring: the value on a class is the alternating sum \
∑_n (-1)^n [H^n(E)] rather than [⊕_n H^{2n}(E)] - [⊕_n H^{2n+1}(E)] (the same element of K_0, \
but the identification of the two expressions is NOT proved here), and X is assumed Noetherian \
regular, the hypotheses of Stacks 0FER, rather than merely locally Noetherian, because the \
global coherence and boundedness of the cohomology sheaves used here come from the converse \
half of Stacks 0FDC. The identification K_0(Coh_Z(X)) = K'_0(Z) is Stacks 0FDT and is NOT \
covered"]
def supportedPerfectEulerHom :
    Pretriangulated.K0 (supportedPerfectDerivedCategory i) →+ KZero (SupportedCoherentModules i) :=
  Classical.choose (exists_supportedPerfectEulerHom i hX)

/-- The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` sends the
class of a perfect complex `E` supported on `Z` to the alternating sum `∑_n (-1)^n [H^n(E)]` of
the classes of its cohomology sheaves. -/
@[stacks 0FEP "the defining property of the homomorphism, in the alternating-sum form"]
theorem supportedPerfectEulerHom_cls (E : supportedPerfectDerivedCategory i) :
    supportedPerfectEulerHom i hX (Pretriangulated.K0.cls E) =
      eulerClass (supportedPerfectDerivedCategory i) (SupportedCoherentModules i)
        (supportedPerfectHomology i hX) E :=
  Classical.choose_spec (exists_supportedPerfectEulerHom i hX) E

/-- The degree-zero cohomology of the direct image of a coherent `𝒪_Z`-module placed in degree
zero is isomorphic to that direct image. -/
def supportedPerfectHomology_obj_singlePushforward
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    (supportedPerfectHomology i hX).obj ((shiftFunctor (supportedPerfectDerivedCategory i)
        (0 : ℤ)).obj (singlePushforwardSupportedPerfect i hX F)) ≅
      (coherentToSupportedCoherent i).obj F := by
  refine (ObjectProperty.fullyFaithfulι (supportedCoherentProperty i)).preimageIso ?_
  refine (ObjectProperty.fullyFaithfulι
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)).preimageIso ?_
  refine ?_ ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (OXMod.{u, u} X.toRingedSpace) 0).app ((Scheme.Modules.pushforward i).obj F.obj)
  refine (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).mapIso
    ((Functor.commShiftIso (ObjectProperty.ι _) (0 : ℤ)).app
      (singlePushforwardSupportedPerfect i hX F)) ≪≫ ?_
  exact ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).shiftIso (0 : ℤ) 0 0
    (add_zero 0)).app (singlePushforwardSupportedPerfect i hX F).obj

/-- Let `X` be a Noetherian regular scheme and `Z ⊂ X` a closed subscheme. The composite of
`coherentToSupportedPerfectHom : K_0(Coh(𝒪_Z)) → K_0(D_{Z, perf}(𝒪_X))` with
`supportedPerfectEulerHom : K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` is the comparison
homomorphism `coherentToSupportedCoherentKZeroHom : K_0(Coh(𝒪_Z)) → K_0(Coh_Z(X))` of direct
image. -/
@[stacks 0FER "the round trip K_0(Coh(Z)) → K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)) is the \
comparison homomorphism of Stacks 0FDT, which is step (1) of the source's proof ('the composite \
is the identity'), stated without the 0FDT identification because that identification is not \
available. What is NOT covered: step (2), surjectivity of K_0(Coh(Z)) → K_0(D_{Z, perf}(O_X)), \
which the source gets from the truncation triangles together with the finite filtration of a \
coherent module supported on Z by O_Z-modules; and therefore NOT the conclusion that the two \
maps are mutually inverse"]
theorem supportedPerfectEulerHom_comp_coherentToSupportedPerfectHom :
    (supportedPerfectEulerHom i hX).comp (coherentToSupportedPerfectHom i hX) =
      coherentToSupportedCoherentKZeroHom i := by
  refine KZero.hom_ext fun F => ?_
  rw [AddMonoidHom.comp_apply, coherentToSupportedPerfectHom_mk,
    coherentToSupportedCoherentKZeroHom_mk, supportedPerfectEulerHom_cls]
  have hvanish : ∀ n : ℤ, n ≠ 0 → ((-1 : ℤ) ^ n.natAbs) •
      KZero.mk (SupportedCoherentModules i) ((supportedPerfectHomology i hX).obj
        ((shiftFunctor (supportedPerfectDerivedCategory i) n).obj
          (singlePushforwardSupportedPerfect i hX F))) = 0 := by
    intro n hn
    rw [KZero.mk_eq_zero_of_isZero (isZero_supportedPerfectHomology_of_isZero i hX
      (singlePushforwardSupportedPerfect i hX F) n
      (DerivedCategory.isZero_homology_singleFunctor_obj
        (C := OXMod.{u, u} X.toRingedSpace) ((Scheme.Modules.pushforward i).obj F.obj) hn)),
      smul_zero]
  rw [eulerClass, finsum_eq_single _ (0 : ℤ) hvanish]
  simpa using KZero.mk_eq_of_iso (supportedPerfectHomology_obj_singlePushforward i hX F)

end AlgebraicGeometry

end
