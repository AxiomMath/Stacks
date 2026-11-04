module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.PreservesInterior
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeCategory
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications

/-!
# The upper shriek functor of a compactification

Let `S` be a quasi-compact quasi-separated scheme (in Situation [Stacks, Tag 0F42], a Noetherian
one) and let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`, the category of schemes
separated and of finite type over `S`. The upper shriek functor of [Stacks, Tag 0A9Y] is built
from a compactification `j` of `X` over `Y`: writing `f̄ = j.toBase : X̄ ⟶ Y` for the proper
structure morphism of the ambient scheme and `ā` for the right adjoint of `Rf̄_*`, it is

  `f^! K = ā(K)|_X`,

the restriction along the open immersion `j.immersion : X ⟶ X̄` of the twisted inverse image
of the compactification, that is the composite `j^* ∘ ā`.

The compactification `j` is an object of `AlgebraicGeometry.CompactificationOf (Over.mk f.left)`,
the category of [Stacks, Tag 0ATU]; its type pins `f` down, `j.immersion ≫ j.toBase = f.left`.
That such a `j` exists is [Stacks, Tag 0F41] (Nagata), and the results here are stated for every
`j`. Everything else the construction needs is proved:

* `Rf̄_*` preserves `D_QCoh` by [Stacks, Tag 08D5],
  `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`;
* the restriction of `Rf̄_*` to `D_QCoh` has a right adjoint by [Stacks, Tag 0A9E], supplied by
  the instance
  `Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`;
* `Lj^*` preserves `D_QCoh` by [Stacks, Tag 08DW], `Stacks.Duality.quasiCoherentDerivedPullback'`.

## Main definitions

* `Stacks.Duality.upperShriek` — **[Stacks, Tag 0A9Y]**, the functor `f^! = j^* ∘ ā` of a
  compactification.
* `Stacks.Duality.properCompactification` — a proper morphism is its own compactification.

## Main results

* `Stacks.Duality.commShift_upperShriek` and `Stacks.Duality.isTriangulated_upperShriek` —
  `f^!` is an exact functor of triangulated categories, which is the assertion the source makes
  about the composite it forms.
* `Stacks.Duality.upperShriekProperIso` and `Stacks.Duality.upperShriekProperAdjunction` — for
  `f` proper and the identity compactification, `f^!` is the right adjoint `a` of
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.
* `Stacks.Duality.twistedInverseImageIdIso` and `Stacks.Duality.quasiCoherentDerivedPullbackIdIso`
  — along the identity, `ā` and `Lj^*` are the identity functor.

## Implementation notes

*The derived categories.* All derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the instance in force on
`Stacks.Duality.quasiCoherentDerivedCategory`: Brown representability, and hence
[Stacks, Tag 0A9E], has content only there, and [Stacks, Tag 08D5] and [Stacks, Tag 08DW] are
proved there. The source constructs `f^!` on `D⁺_QCoh`; both factors of the composite are defined
on the unbounded `D_QCoh`, so the functor below is defined there and restricts to the source's.

*The base.* The source takes `S` Noetherian. The construction uses only that `S` is
quasi-compact and quasi-separated, which makes `Y` and `X̄` quasi-compact and quasi-separated as
[Stacks, Tag 0A9E] requires; the statements are made under that weaker hypothesis.

*Exactness.* `ā` is a right adjoint of the exact functor `Rf̄_*`, and `Lj^*` is a left adjoint
of the exact functor `Rj_*`; the shift compatibilities are the unique ones compatible with
the two adjunctions, and exactness of a composite is formal.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### Derived pullback and derived direct image along the identity -/

section Identity

variable (Y : Scheme.{u})

/-- Degreewise pullback of sheaves of modules along the identity is left exact: it is isomorphic
to the identity functor. -/
theorem preservesFiniteLimits_pullback_id :
    PreservesFiniteLimits (Scheme.Modules.pullback (𝟙 Y)) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.pullbackId Y).symm

/-- **Derived pullback along the identity is the identity.** Degreewise pullback along `𝟙_Y` is
exact, so `L(𝟙_Y)^*` is its derived functor degreewise; and degreewise pullback along `𝟙_Y` is
the identity. -/
def derivedPullbackIdIso : derivedPullback (𝟙 Y) ≅ 𝟭 (DerivedCategory Y.Modules) :=
  have := preservesFiniteLimits_pullback_id Y
  have := AlgebraicGeometry.preservesFiniteColimits_modulesPullback (𝟙 Y)
  derivedPullbackMapDerivedIso (𝟙 Y) ≪≫
    Functor.mapDerivedCategoryCongr (Scheme.Modules.pullbackId Y) ≪≫
      Functor.mapDerivedCategoryId Y.Modules

/-- **Derived direct image along the identity is the identity.** `R(𝟙_Y)_*` is a right adjoint of
`L(𝟙_Y)^*`, which is the identity functor, and the identity functor is a right adjoint of itself;
right adjoints are unique up to canonical isomorphism. -/
def derivedPushforwardIdIso : derivedPushforward (𝟙 Y) ≅ 𝟭 (DerivedCategory Y.Modules) :=
  Adjunction.rightAdjointUniq
    ((derivedAdjunction (𝟙 Y)).ofNatIsoLeft (derivedPullbackIdIso Y)) Adjunction.id

/-- **Derived pullback along the identity is the identity on `D_QCoh(𝒪_Y)`**: the ambient
isomorphism `Stacks.Duality.derivedPullbackIdIso` read on the full subcategory. -/
def quasiCoherentDerivedPullbackIdIso
    (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPullback (𝟙 Y)).obj K.obj)).IsQuasicoherent) :
    quasiCoherentDerivedPullback (𝟙 Y) hpull ≅ 𝟭 (quasiCoherentDerivedCategory Y) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPullbackIdIso Y).app K.obj))
    fun e => ObjectProperty.hom_ext _ ((derivedPullbackIdIso Y).hom.naturality e.hom)

variable (hpush : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (𝟙 Y)).obj K.obj)).IsQuasicoherent)

/-- **Derived direct image along the identity is the identity on `D_QCoh(𝒪_Y)`**: the ambient
isomorphism read on the full subcategory of complexes with quasi-coherent cohomology. -/
def quasiCoherentDerivedPushforwardIdIso :
    quasiCoherentDerivedPushforward (𝟙 Y) hpush ≅ 𝟭 (quasiCoherentDerivedCategory Y) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPushforwardIdIso Y).app K.obj))
    fun e => ObjectProperty.hom_ext _ ((derivedPushforwardIdIso Y).hom.naturality e.hom)

/-- **[Stacks, Tag 0A9E] for the identity morphism, on any scheme**: the restriction of
`R(𝟙_Y)_*` to `D_QCoh(𝒪_Y)` has a right adjoint, namely the identity functor. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_id :
    (quasiCoherentDerivedPushforward (𝟙 Y) hpush).IsLeftAdjoint :=
  ⟨⟨𝟭 (quasiCoherentDerivedCategory Y),
    ⟨Adjunction.id.ofNatIsoLeft (quasiCoherentDerivedPushforwardIdIso Y hpush).symm⟩⟩⟩

/-- **The twisted inverse image of the identity is the identity.** This is the step the proof of
[Stacks, Tag 0AU0] calls "the right adjoint of Lemma 48.3.1 applied to `id : Y ⟶ Y` is the
identity functor": `R(𝟙_Y)_*` on `D_QCoh(𝒪_Y)` is the identity, so its right adjoint is. -/
def twistedInverseImageIdIso :
    twistedInverseImage (𝟙 Y) hpush ≅ 𝟭 (quasiCoherentDerivedCategory Y) :=
  Adjunction.rightAdjointUniq
    ((twistedInverseImageAdjunction (𝟙 Y) hpush).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardIdIso Y hpush)) Adjunction.id

end Identity

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- A compactification of `X` over `Y` factors the morphism it compactifies: `j.obj.hom` is a
morphism of schemes over `Y.left`, so the open immersion followed by the structure morphism of
the ambient scheme is `f` itself. This is what ties `Stacks.Duality.upperShriek` to `f`: `j` is
not arbitrary data on the side but a factorisation of `f` through a proper morphism. -/
theorem immersion_comp_toBase : j.immersion ≫ j.toBase = f.left := by
  simp [CompactificationOf.immersion, CompactificationOf.toBase]

section UpperShriek

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- Over a quasi-compact quasi-separated base the open immersion of a compactification is
quasi-compact: its source is quasi-compact and its target quasi-separated. -/
instance quasiCompact_immersion : QuasiCompact j.immersion :=
  @quasiCompact_of_compactSpace _ _ j.immersion (inferInstanceAs (CompactSpace X.left)) _

/-- **Stacks Project, Tag 0A9Y.** The upper shriek functor of a compactification. Let `S` be a
quasi-compact quasi-separated scheme (in the source, a Noetherian one), let `f : X ⟶ Y` be a
morphism of schemes separated and of finite type over `S` and let `j` be a compactification of
`X` over `Y`, with open immersion `j.immersion : X ⟶ X̄` and proper structure morphism
`f̄ = j.toBase : X̄ ⟶ Y`. Let `ā` be the right adjoint of `Rf̄_* : D_QCoh(𝒪_X̄) ⥤ D_QCoh(𝒪_Y)`
of [Stacks, Tag 0A9E]. Then `f^! K = ā(K)|_X`, that is `f^! = j^* ∘ ā`. -/
@[stacks 0A9Y]
def upperShriek :
    quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left :=
  twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase) ⋙
    quasiCoherentDerivedPullback' j.immersion

/-- The value of `f^!` on an object is the restriction to `X` of the twisted inverse image of
the compactification, by definition of the composite. -/
theorem upperShriek_obj (K : quasiCoherentDerivedCategory Y.left) :
    (upperShriek f j).obj K =
      (quasiCoherentDerivedPullback' j.immersion).obj
        ((twistedInverseImage j.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj K) :=
  rfl

/-- `f^!` commutes with the shift. The right adjoint `ā` carries the unique shift
compatibility compatible with `Rf̄_* ⊣ ā`, the left adjoint `Lj^*` the unique one compatible
with `Lj^* ⊣ Rj_*`, and a composite of functors commuting with the shift commutes with it. -/
instance commShift_upperShriek : (upperShriek f j).CommShift ℤ :=
  let := (twistedInverseImageAdjunction j.toBase
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).rightAdjointCommShift ℤ
  let := commShift_quasiCoherentDerivedPullback j.immersion
    (isQuasicoherent_homology_derivedPullback' j.immersion)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion)
  inferInstanceAs ((twistedInverseImage j.toBase
    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase) ⋙
      quasiCoherentDerivedPullback' j.immersion).CommShift ℤ)

/-- **`f^!` is an exact functor of triangulated categories**, which is what the source
asserts about the composite `j^* ∘ ā`. The right adjoint of the exact functor `Rf̄_*` is
exact, the left adjoint of the exact functor `Rj_*` is exact, and a composite of exact
functors is exact. -/
instance isTriangulated_upperShriek : (upperShriek f j).IsTriangulated := by
  have hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase
  have hpull := isQuasicoherent_homology_derivedPullback' j.immersion
  have hpushImm := isQuasicoherent_homology_derivedPushforward_of_qcqs j.immersion
  let := (twistedInverseImageAdjunction j.toBase hpush).rightAdjointCommShift ℤ
  let := (twistedInverseImageAdjunction j.toBase hpush).commShift_of_leftAdjoint ℤ
  have : (twistedInverseImage j.toBase hpush).IsTriangulated :=
    (twistedInverseImageAdjunction j.toBase hpush).isTriangulated_rightAdjoint
  let := commShift_quasiCoherentDerivedPullback j.immersion hpull hpushImm
  let := (quasiCoherentDerivedAdjunction j.immersion hpull hpushImm).commShift_of_rightAdjoint ℤ
  have : (quasiCoherentDerivedPullback j.immersion hpull).IsTriangulated :=
    (quasiCoherentDerivedAdjunction j.immersion hpull hpushImm).isTriangulated_leftAdjoint
  exact inferInstanceAs ((twistedInverseImage j.toBase hpush ⋙
    quasiCoherentDerivedPullback j.immersion hpull).IsTriangulated)

end UpperShriek

/-! ### A proper morphism is its own compactification -/

/-- A proper morphism of `AlgebraicGeometry.FTS S` is its own compactification: the identity
is an open immersion and the structure morphism is proper. This exhibits an object of
`AlgebraicGeometry.CompactificationOf (Over.mk f.left)`, so the quantification over
compactifications in `Stacks.Duality.upperShriek` is over a nonempty category for such `f`. -/
def properCompactification [IsProper f.left] :
    AlgebraicGeometry.CompactificationOf (Over.mk f.left) :=
  ⟨StructuredArrow.mk (𝟙 (Over.mk f.left)), ⟨inferInstanceAs (IsOpenImmersion (𝟙 X.left)),
    inferInstanceAs (IsProper f.left)⟩⟩

/-- The space of `properCompactification f` is the source `X.left` of `f`. -/
@[simp]
theorem properCompactification_space [IsProper f.left] :
    (properCompactification f).space = X.left :=
  rfl

/-- The proper structure morphism of `properCompactification f` is `f.left`. -/
@[simp]
theorem properCompactification_toBase [IsProper f.left] :
    (properCompactification f).toBase = f.left :=
  rfl

/-- The open immersion of `properCompactification f` is the identity of `X.left`. -/
@[simp]
theorem properCompactification_immersion [IsProper f.left] :
    (properCompactification f).immersion = 𝟙 X.left :=
  rfl

/-! ### The upper shriek of a proper morphism is the right adjoint of `Rf_*` -/

section Proper

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f.left]

/-- **For a proper morphism, `f^!` at the identity compactification is the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.** With `X̄ = X` the open immersion is `𝟙_X`, and `L(𝟙_X)^*`
is the identity of `D_QCoh(𝒪_X)`. -/
def upperShriekProperIso :
    upperShriek f (properCompactification f) ≅
      twistedInverseImage f.left (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left) :=
  Functor.isoWhiskerLeft
      (twistedInverseImage f.left (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left))
      (quasiCoherentDerivedPullbackIdIso X.left _) ≪≫ Functor.rightUnitor _

/-- **For a proper morphism, `f^!` at the identity compactification is right adjoint to
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.** -/
def upperShriekProperAdjunction :
    DerivedPushforward.qcqsRestrictedDerivedPushforward f.left ⊣
      upperShriek f (properCompactification f) :=
  (twistedInverseImageAdjunction f.left
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left)).ofNatIsoRight
      (upperShriekProperIso f).symm

end Proper

end Stacks.Duality

end
