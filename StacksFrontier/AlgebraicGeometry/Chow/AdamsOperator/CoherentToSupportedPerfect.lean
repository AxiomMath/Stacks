module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.CoherentInclusionExact
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AbelianCategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RegularPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# From coherent sheaves on a closed subscheme to perfect complexes supported on it

Let `i : Z ⟶ X` be a closed immersion of schemes with `X` regular. A coherent `𝒪_Z`-module `ℱ`
has a direct image `i_*ℱ`, which is a coherent `𝒪_X`-module; placed in degree zero it is an
object `(i_*ℱ)[0]` of the derived category of `𝒪_X`-modules which is perfect, because `X` is
regular, and whose cohomology sheaves are supported on the closed subset underlying `Z`. So it
lies in `D_{Z, perf}(𝒪_X)`. A short exact sequence `0 → ℱ → ℱ' → ℱ'' → 0` of coherent
`𝒪_Z`-modules has exact direct image and therefore gives a distinguished triangle
`(i_*ℱ)[0] → (i_*ℱ')[0] → (i_*ℱ'')[0] → (i_*ℱ)[1]`, so `[ℱ] ↦ [(i_*ℱ)[0]]` respects the
defining relations of the Grothendieck group and induces a canonical homomorphism
`K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))`.

## Main definitions

* `AlgebraicGeometry.singlePushforwardSupportedPerfect` is the object `(i_*ℱ)[0]` of
  `D_{Z, perf}(𝒪_X)` attached to a coherent `𝒪_Z`-module `ℱ`.
* `AlgebraicGeometry.coherentToSupportedPerfectHom` is the canonical homomorphism
  `K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))`.

## Main results

* `AlgebraicGeometry.coherentToSupportedPerfectHom_mk` computes the homomorphism on the class
  of a coherent `𝒪_Z`-module: it is the class of `(i_*ℱ)[0]`.
* `AlgebraicGeometry.cls_singlePushforwardSupportedPerfect_add` is the additivity along a short
  exact sequence of coherent modules which makes the homomorphism well defined.
* `CategoryTheory.Pretriangulated.K0.cls_add_of_distinguished`: in the `K`-group of a
  triangulated subcategory, the class of the middle object of a distinguished triangle of the
  ambient category whose three objects lie in the subcategory is the sum of the classes of the
  outer two.
* `DerivedCategory.isZero_homology_singleFunctor_obj`: an object of an abelian category placed
  in degree zero has vanishing cohomology in every nonzero degree.

## Implementation notes

Perfectness of `(i_*ℱ)[0]` is `AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`,
the degree-zero case of the forward half of [Stacks, Tag 0FDC], applied to the coherent module
`i_*ℱ`; coherence of `i_*ℱ` is [Stacks, Tag 087T]
(`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`). The two local Noetherian
hypotheses this chain needs are not assumed: regularity of `X` gives
`AlgebraicGeometry.isLocallyNoetherian_of_isRegular`, and that in turn gives local
Noetherianity of `Z` through `AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`.

The support condition is checked degreewise. In degree zero the cohomology sheaf of `(i_*ℱ)[0]`
is `i_*ℱ` by `DerivedCategory.singleFunctorCompHomologyFunctorIso`, and the direct image along a
closed immersion has vanishing stalks off the image, which is
`AlgebraicGeometry.notMem_supp_pushforward_of_notMemRange`. In every other degree the cohomology
sheaf vanishes and its support is empty.

Exactness of the functor `ℱ ↦ i_*ℱ` from coherent `𝒪_Z`-modules to `𝒪_X`-modules is the
composite of exactness of the inclusion of coherent modules, which is the weak Serre property
of [Stacks, Tag 01BY], with exactness of the direct image along a closed immersion, which is
[Stacks, Tag 08KS]: left exactness because the direct image is a right adjoint, right exactness
from `AlgebraicGeometry.Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion`.
The distinguished triangle of a short exact sequence is Mathlib's
`CategoryTheory.ShortComplex.ShortExact.singleTriangle`.

The passage from that triangle, which lives in `D(𝒪_X)`, to the relation in the `K`-group of the
subcategory `D_{Z, perf}(𝒪_X)` is isolated in
`CategoryTheory.Pretriangulated.K0.cls_add_of_distinguished`: the distinguished triangles of a
triangulated subcategory are by definition those whose image under the inclusion is
distinguished, so the three morphisms are taken along the full and faithful inclusion and the
connecting morphism is corrected by the shift-commutation isomorphism.

## References

* [Stacks Project, Tag 0FEQ](https://stacks.math.columbia.edu/tag/0FEQ)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect

universe w v u

namespace DerivedCategory

/-- **The cohomology of an object placed in degree zero vanishes away from degree zero.** For an
object `A` of an abelian category, the `n`-th cohomology of `A[0]` is the `n`-th homology of the
cochain complex with `A` in degree zero, which is zero for `n ≠ 0` because that complex is
concentrated in degree zero. -/
theorem isZero_homology_singleFunctor_obj {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (A : C) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((homologyFunctor C n).obj ((singleFunctor C 0).obj A)) := by
  refine IsZero.of_iso ?_
    ((homologyFunctorFactors C n).app ((CochainComplex.singleFunctor C 0).obj A))
  rcases lt_or_gt_of_ne hn with h | h
  · exact CochainComplex.isZero_of_isGE _ 0 n h
  · exact CochainComplex.isZero_of_isLE _ 0 n h

end DerivedCategory

namespace CategoryTheory.Pretriangulated.K0

/-- **Additivity of classes along a distinguished triangle of a triangulated subcategory.** Let
`P` be a triangulated subcategory of a pretriangulated category `D` and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]`
be a distinguished triangle of `D` all three of whose objects lie in `P`. Then
`[E₂] = [E₁] + [E₃]` in `K₀(P)`.

The distinguished triangles of `P` are those whose image under the inclusion is distinguished, so
the triangle of `P` is assembled from the preimages of the three morphisms under the full and
faithful inclusion, the connecting morphism being corrected by the shift-commutation
isomorphism of the inclusion. -/
theorem cls_add_of_distinguished {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {P : ObjectProperty D} [P.IsTriangulated] (E₁ E₂ E₃ : P.FullSubcategory)
    (f : E₁.obj ⟶ E₂.obj) (g : E₂.obj ⟶ E₃.obj) (h : E₃.obj ⟶ (E₁.obj)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang D) :
    cls E₂ = cls E₁ + cls E₃ := by
  let T : Triangle P.FullSubcategory := Triangle.mk
    (P.fullyFaithfulι.preimage (X := E₁) (Y := E₂) f)
    (P.fullyFaithfulι.preimage (X := E₂) (Y := E₃) g)
    (P.fullyFaithfulι.preimage (X := E₃) (Y := E₁⟦(1 : ℤ)⟧)
      (h ≫ ((ObjectProperty.ι P).commShiftIso (1 : ℤ)).inv.app E₁))
  have hT' : T ∈ distTriang P.FullSubcategory := by
    show (ObjectProperty.ι P).mapTriangle.obj T ∈ distTriang D
    simpa [T] using hT
  rw [← sub_eq_zero, ← sub_sub]
  exact cls_rel T hT'

/-- **Additivity of classes along a short exact sequence placed in degree zero.** Let `P` be a
triangulated subcategory of the derived category of an abelian category `C` and let
`0 → X₁ → X₂ → X₃ → 0` be a short exact sequence in `C` whose three terms, placed in degree zero,
are objects `E₁`, `E₂`, `E₃` of `P`. Then `[E₂] = [E₁] + [E₃]` in `K₀(P)`.

The distinguished triangle is the one `CategoryTheory.ShortComplex.ShortExact.singleTriangle`
attaches to the short exact sequence. -/
theorem cls_add_of_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {P : ObjectProperty (DerivedCategory C)} [P.IsTriangulated]
    {S : ShortComplex C} (hS : S.ShortExact) (E₁ E₂ E₃ : P.FullSubcategory)
    (h₁ : E₁.obj = (DerivedCategory.singleFunctor C 0).obj S.X₁)
    (h₂ : E₂.obj = (DerivedCategory.singleFunctor C 0).obj S.X₂)
    (h₃ : E₃.obj = (DerivedCategory.singleFunctor C 0).obj S.X₃) :
    cls E₂ = cls E₁ + cls E₃ := by
  obtain ⟨O₁, p₁⟩ := E₁
  obtain ⟨O₂, p₂⟩ := E₂
  obtain ⟨O₃, p₃⟩ := E₃
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  exact cls_add_of_distinguished _ _ _ _ _ hS.singleδ hS.singleTriangle_distinguished

end CategoryTheory.Pretriangulated.K0

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (hX : IsRegular X)

/-- **A coherent module on a closed subscheme of a regular scheme, pushed forward and placed in
degree zero, is a perfect complex supported on that subscheme.** The direct image `i_*ℱ` of a
coherent `𝒪_Z`-module `ℱ` is coherent by [Stacks, Tag 087T], hence `(i_*ℱ)[0]` is a perfect
object of `D(𝒪_X)` by the degree-zero case of [Stacks, Tag 0FDC]; its cohomology sheaf in degree
zero is `i_*ℱ`, whose stalks vanish off the image of `i`, and its cohomology sheaves in all
other degrees vanish. -/
def singlePushforwardSupportedPerfect (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
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
theorem singlePushforwardSupportedPerfect_obj
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    (singlePushforwardSupportedPerfect i hX F).obj =
      (DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
        ((Scheme.Modules.pushforward i).obj F.obj) :=
  rfl

/-- **The class of `(i_*ℱ)[0]` is additive along short exact sequences of coherent modules.** The
functor taking a coherent `𝒪_Z`-module to its direct image is exact, being the composite of the
exact inclusion of coherent modules into all `𝒪_Z`-modules ([Stacks, Tag 01BY]) with the exact
direct image along a closed immersion ([Stacks, Tag 08KS]), so a short exact sequence of coherent
`𝒪_Z`-modules gives a short exact sequence of `𝒪_X`-modules and hence a distinguished triangle of
the three direct images placed in degree zero. -/
theorem cls_singlePushforwardSupportedPerfect_add
    (S : ShortComplex (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf))
    (hS : S.ShortExact) :
    Pretriangulated.K0.cls (singlePushforwardSupportedPerfect i hX S.X₂) =
      Pretriangulated.K0.cls (singlePushforwardSupportedPerfect i hX S.X₁) +
        Pretriangulated.K0.cls (singlePushforwardSupportedPerfect i hX S.X₃) := by
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} i.toRingCatSheafHom) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward i))
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} i.toRingCatSheafHom) :=
    Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedImmersion i
  have : (SheafOfModules.pushforward.{u} i.toRingCatSheafHom).PreservesZeroMorphisms :=
    inferInstanceAs ((Scheme.Modules.pushforward i).PreservesZeroMorphisms)
  have : (ObjectProperty.ι
      (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_full _
  have hS₁ := hS.map_of_exact
    (ObjectProperty.ι (Stacks.SheafOfModules.coherentModules Z.ringCatSheaf))
  have hS₂ := hS₁.map_of_exact (SheafOfModules.pushforward.{u} i.toRingCatSheafHom)
  exact Pretriangulated.K0.cls_add_of_shortExact (C := OXMod.{u, u} X.toRingedSpace) hS₂
    (singlePushforwardSupportedPerfect i hX S.X₁) (singlePushforwardSupportedPerfect i hX S.X₂)
    (singlePushforwardSupportedPerfect i hX S.X₃) rfl rfl rfl

/-- **Stacks Project, Tag 0FEQ.** Let `i : Z ⟶ X` be a closed immersion of schemes with `X`
regular. There is a canonical homomorphism `K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))` taking the class
of a coherent `𝒪_Z`-module `ℱ` to the class of its direct image placed in degree zero.

The source is the Grothendieck group of the abelian category of coherent `𝒪_Z`-modules and the
target is the `K`-group of the triangulated category of perfect complexes on `X` supported on the
closed subset underlying `Z`. The map is well defined because the direct image of a short exact
sequence of coherent modules is short exact, hence gives a distinguished triangle of the three
degree-zero complexes. -/
@[stacks 0FEQ]
def coherentToSupportedPerfectHom :
    KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) →+
      Pretriangulated.K0 (supportedPerfectDerivedCategory i) :=
  KZero.lift (fun F => Pretriangulated.K0.cls (singlePushforwardSupportedPerfect i hX F))
    (cls_singlePushforwardSupportedPerfect_add i hX)

/-- **Stacks Project, Tag 0FEQ.** The canonical homomorphism
`K₀(Coh(𝒪_Z)) → K₀(D_{Z, perf}(𝒪_X))` takes the class of a coherent `𝒪_Z`-module `ℱ` to the class
of the perfect complex `(i_*ℱ)[0]`. -/
@[simp, stacks 0FEQ]
theorem coherentToSupportedPerfectHom_mk
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    coherentToSupportedPerfectHom i hX (KZero.mk _ F) =
      Pretriangulated.K0.cls (singlePushforwardSupportedPerfect i hX F) :=
  KZero.lift_mk _ _ _

end AlgebraicGeometry

end
