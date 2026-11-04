module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAlgebraFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct-image functor onto the bounded quasi-coherent algebras

Stacks 081V asserts an anti-equivalence between the algebraic spaces affine over an algebraic
space `X` and the quasi-coherent sheaves of commutative `𝒪_X`-algebras, sending `f : Y ⟶ X` to
`f_* 𝒪_Y`.  For `Y` affine over `X` the ring `f_* 𝒪_Y (V)` has fewer than `B.cutoff` elements at
every étale chart `V` of `X`, `B.cutoff` being the cardinal of the ambient big fppf site.  This
file takes as target the quasi-coherent algebras `𝒜` with fewer than `B.cutoff` sections at every
étale chart of `X`, shows that this size condition is satisfied exactly by the algebras the
direct image can produce, and reduces the anti-equivalence onto that target to statements about
the unrestricted direct-image functor.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff`: the size condition
  `∀ V, #(𝒜(V)) < B.cutoff`, over the objects `V` of the small étale site of `X`.
* `AlgebraicGeometry.Space.BoundedQuasicoherentAlgebra`: the quasi-coherent `𝒪_X`-algebras
  satisfying that condition, and `AlgebraicGeometry.Space.boundedQuasicoherentAlgebraInclusion`
  its inclusion into `AlgebraicGeometry.Space.QuasicoherentAlgebra`.
* `AlgebraicGeometry.Space.boundedPushforwardAlgebraFunctor`: the contravariant direct-image
  functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the bounded quasi-coherent
  `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence`: an anti-equivalence between the
  algebraic spaces affine over `X` and the bounded quasi-coherent `𝒪_X`-algebras, naturally
  identified with direct image, with the field names of
  `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`.
* `AlgebraicGeometry.Space.boundedAffineAlgebraAntiEquivalenceOfIsEquivalence`: such an
  anti-equivalence, built from the bounded direct-image functor being an equivalence.
* `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence.relativeSpec`: the relative
  spectrum of a bounded quasi-coherent algebra, read off a bounded anti-equivalence.

## Main results

* `AlgebraicGeometry.Space.sectionsBelowCutoff_of_mem_essImage`: every quasi-coherent
  `𝒪_X`-algebra isomorphic to some `f_* 𝒪_Y` with `f` affine satisfies the size condition.
* `Space.not_mem_essImage_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections` and
  `Space.not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections`: an algebra with
  at least `B.cutoff` sections over one chart is not a direct image, so then the unrestricted
  direct-image functor is not essentially surjective.
* `AlgebraicGeometry.Space.essImage_boundedPushforwardAlgebraFunctor_iff`: the bounded
  direct-image functor has the same essential image as the unrestricted one.
* `AlgebraicGeometry.Space.essSurj_boundedPushforwardAlgebraFunctor_iff`: the bounded functor
  is essentially surjective exactly when every quasi-coherent algebra satisfying the size
  condition is a direct image.
* `AlgebraicGeometry.Space.nonempty_boundedQuasicoherentAlgebra`: the bounded category is not
  empty.
* `AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor_iff` and
  `AlgebraicGeometry.Space.faithful_boundedPushforwardAlgebraFunctor_iff`: the bounded functor
  is full, respectively faithful, exactly when the unrestricted one is.
* `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff`: the bounded
  functor is an equivalence exactly when the unrestricted one is full, faithful, and reaches
  every quasi-coherent algebra satisfying the size condition.
* `AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor_iff` and
  `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff`: the direct-image functor
  is faithful exactly when `AlgebraicGeometry.Space.pushforwardRingMap` is injective on the
  morphisms over `X` between objects affine over `X`, and full exactly when
  `AlgebraicGeometry.Space.pushforwardAlgebraMap` is surjective onto the morphisms between their
  direct-image algebras.
* `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective`: the
  bounded functor is an equivalence exactly when `f ↦ f_*` is a bijection from the morphisms over
  `X` between objects affine over `X` onto the morphisms of their direct-image algebras, and
  every quasi-coherent algebra satisfying the size condition is a direct image.
* `AlgebraicGeometry.Space.essImage_affinePushforwardAlgebraFunctor_of_bounded` and
  `AlgebraicGeometry.Space.essSurj_boundedPushforwardAlgebraFunctor_of`: given a bounded
  anti-equivalence, every quasi-coherent algebra satisfying the size condition is a direct image.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The size condition and the category it cuts out -/

/-- A sheaf of `𝒪_X`-algebras has sections below the cutoff when at every étale chart `V` of `X`
the ring `𝒜(V)` has fewer than `B.cutoff` elements, `B.cutoff` being the single cardinal that
defines membership of the ambient big fppf site (`AlgebraicGeometry.BigFppfSite.Contains`). -/
abbrev AlgebraSheaf.SectionsBelowCutoff {X : AlgebraicSpaces B S hS}
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) : Prop :=
  ∀ V : SmallEtale B S hS X.1, #(A.right.obj.obj (op V)) < B.cutoff

/-- The category of quasi-coherent sheaves of commutative `𝒪_X`-algebras whose sections at every
étale chart of `X` are fewer than the cutoff of the ambient big fppf site. -/
abbrev BoundedQuasicoherentAlgebra (X : AlgebraicSpaces B S hS) :=
  ObjectProperty.FullSubcategory
    (fun A : QuasicoherentAlgebra B S hS X =>
      AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)

/-- The inclusion of the bounded quasi-coherent algebras on `X` into all quasi-coherent algebras on
`X`. -/
abbrev boundedQuasicoherentAlgebraInclusion (X : AlgebraicSpaces B S hS) :
    BoundedQuasicoherentAlgebra B S hS X ⥤ QuasicoherentAlgebra B S hS X :=
  ObjectProperty.ι
    (fun A : QuasicoherentAlgebra B S hS X =>
      AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)

/-! ### The size condition is invariant, and is satisfied exactly by the direct images -/

/-- Isomorphic quasi-coherent algebras have equally many sections over every étale chart: the
isomorphism is read through the forgetful functors to the underlying sheaf of rings, to its
presheaf, to the ring of sections at the chart, and to types. -/
theorem mk_sections_eq_of_iso {X : AlgebraicSpaces B S hS}
    {A C : QuasicoherentAlgebra B S hS X} (i : A ≅ C) (V : SmallEtale B S hS X.1) :
    #(A.obj.right.obj.obj (op V)) = #(C.obj.right.obj.obj (op V)) :=
  mk_congr ((forget CommRingCat.{u}).mapIso
    ((quasicoherentAlgebraInclusion B S hS X ⋙
        AlgebraSheaf.forget (B := B) (S := S) (hS := hS) (F := X.1) (hF := X.2) ⋙
        sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)).mapIso i)).toEquiv

/-- Every quasi-coherent `𝒪_X`-algebra in the essential image of the direct-image functor — that
is, every one isomorphic to `f_* 𝒪_Y` for some algebraic space `Y` affine over `X` — has fewer than
`B.cutoff` sections at every étale chart of `X`. -/
theorem sectionsBelowCutoff_of_mem_essImage {X : AlgebraicSpaces B S hS}
    {A : QuasicoherentAlgebra B S hS X}
    (hA : (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A) :
    AlgebraSheaf.SectionsBelowCutoff B S hS A.obj := by
  obtain ⟨Y, ⟨i⟩⟩ := hA
  intro V
  rw [← mk_sections_eq_of_iso B S hS i V]
  exact mk_sections_pushforwardAlgebra_lt_cutoff B S hS Y.unop.obj V

/-- A quasi-coherent `𝒪_X`-algebra with at least `B.cutoff` sections over a single étale chart of
`X` is not isomorphic to `f_* 𝒪_Y` for any algebraic space `Y` affine over `X`. -/
theorem not_mem_essImage_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections
    {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1)
    (A : QuasicoherentAlgebra B S hS X)
    (hA : B.cutoff ≤ #(A.obj.right.obj.obj (op V))) :
    ¬ (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A :=
  fun h => absurd hA (not_le.2 (sectionsBelowCutoff_of_mem_essImage B S hS h V))

/-- The unrestricted direct-image functor is not essentially surjective as soon as one
quasi-coherent `𝒪_X`-algebra has at least `B.cutoff` sections over one étale chart of `X`. -/
theorem not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections
    {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1)
    (A : QuasicoherentAlgebra B S hS X)
    (hA : B.cutoff ≤ #(A.obj.right.obj.obj (op V))) :
    ¬ (quasicoherentPushforwardAlgebraFunctor B S hS X).EssSurj :=
  fun h => not_mem_essImage_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections
    B S hS V A hA (h.mem_essImage A)

/-! ### The direct-image functor into the bounded algebras -/

/-- The contravariant functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the
quasi-coherent sheaves of commutative `𝒪_X`-algebras *whose sections at every étale chart of `X`
are fewer than the cutoff of the ambient big fppf site*. -/
@[stacks 081V "the direct image functor f ↦ f_* 𝒪_Y from the algebraic spaces affine over X, \
in the corrected form with the target restricted to the quasi-coherent 𝒪_X-algebras whose \
sections at every étale chart of X number fewer than the big fppf site's cutoff — the bound the \
direct image of an affine morphism satisfies by construction, and which the tag's unrestricted \
target fails (not_essSurj_affinePushforwardAlgebraFunctor_of_cutoff_le_mk_sections).  This \
registration is the functor itself; its faithfulness, fullness and essential surjectivity are \
faithful_affinePushforwardAlgebraFunctor, full_affinePushforwardAlgebraFunctor and \
essSurj_boundedPushforwardAlgebraFunctor (via boundedRelativeSpec, Stacks 081W), and the \
base-change compatibility is the subject of the other 081V registrations",
  sga "3 III 0.1.7" "more general"]
def boundedPushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ⥤ BoundedQuasicoherentAlgebra B S hS X :=
  ObjectProperty.lift
    (fun A : QuasicoherentAlgebra B S hS X =>
      AlgebraSheaf.SectionsBelowCutoff B S hS A.obj)
    (quasicoherentPushforwardAlgebraFunctor B S hS X)
    fun Y V => mk_sections_pushforwardAlgebra_lt_cutoff B S hS Y.unop.obj V

/-- The bounded direct-image functor is the unrestricted one: cutting the codomain down to the
algebras satisfying the size condition changes nothing but the codomain. -/
theorem boundedPushforwardAlgebraFunctor_comp_ι (X : AlgebraicSpaces B S hS) :
    boundedPushforwardAlgebraFunctor B S hS X ⋙ boundedQuasicoherentAlgebraInclusion B S hS X =
      quasicoherentPushforwardAlgebraFunctor B S hS X :=
  rfl

/-- A bounded quasi-coherent `𝒪_X`-algebra is in the essential image of the bounded direct-image
functor exactly when it is in the essential image of the unrestricted one. -/
theorem essImage_boundedPushforwardAlgebraFunctor_iff {X : AlgebraicSpaces B S hS}
    (A : BoundedQuasicoherentAlgebra B S hS X) :
    (boundedPushforwardAlgebraFunctor B S hS X).essImage A ↔
      (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A.obj :=
  ⟨fun ⟨Y, ⟨i⟩⟩ => ⟨Y, ⟨(boundedQuasicoherentAlgebraInclusion B S hS X).mapIso i⟩⟩,
    fun ⟨Y, ⟨i⟩⟩ => ⟨Y, ⟨(boundedQuasicoherentAlgebraInclusion B S hS X).preimageIso i⟩⟩⟩

/-- The bounded direct-image functor is essentially surjective exactly when every quasi-coherent
`𝒪_X`-algebra whose sections at every étale chart of `X` are fewer than the cutoff is isomorphic to
`f_* 𝒪_Y` for some algebraic space `Y` affine over `X`. -/
theorem essSurj_boundedPushforwardAlgebraFunctor_iff {X : AlgebraicSpaces B S hS} :
    (boundedPushforwardAlgebraFunctor B S hS X).EssSurj ↔
      ∀ A : QuasicoherentAlgebra B S hS X, AlgebraSheaf.SectionsBelowCutoff B S hS A.obj →
        (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A :=
  ⟨fun h A hA => (essImage_boundedPushforwardAlgebraFunctor_iff B S hS ⟨A, hA⟩).1
      (h.mem_essImage ⟨A, hA⟩),
    fun h => ⟨fun A =>
      (essImage_boundedPushforwardAlgebraFunctor_iff B S hS A).2 (h A.obj A.property)⟩⟩

/-- The category of bounded quasi-coherent algebras on `X` is not empty. -/
theorem nonempty_boundedQuasicoherentAlgebra (X : AlgebraicSpaces B S hS) :
    Nonempty (BoundedQuasicoherentAlgebra B S hS X) :=
  ⟨(boundedPushforwardAlgebraFunctor B S hS X).obj (op (idAffineOver B S hS X))⟩

/-! ### The bounded form of Stacks 081V, reduced to the unrestricted functor -/

/-- The size condition is invariant under isomorphism of quasi-coherent algebras, so the bounded
algebras are a replete full subcategory. -/
instance isClosedUnderIsomorphisms_sectionsBelowCutoff (X : AlgebraicSpaces B S hS) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : QuasicoherentAlgebra B S hS X =>
        AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) where
  of_iso i hA V := (mk_sections_eq_of_iso B S hS i V) ▸ hA V

/-- The bounded direct-image functor is faithful exactly when the unrestricted one is. -/
theorem faithful_boundedPushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).Faithful ↔
      (quasicoherentPushforwardAlgebraFunctor B S hS X).Faithful := by
  constructor
  · intro h
    exact Functor.Faithful.comp (boundedPushforwardAlgebraFunctor B S hS X)
      (boundedQuasicoherentAlgebraInclusion B S hS X)
  · intro h
    exact Functor.Faithful.of_comp_eq (boundedPushforwardAlgebraFunctor_comp_ι B S hS X)

/-- The bounded direct-image functor is full exactly when the unrestricted one is. -/
theorem full_boundedPushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).Full ↔
      (quasicoherentPushforwardAlgebraFunctor B S hS X).Full := by
  constructor
  · intro h
    exact Functor.Full.comp (boundedPushforwardAlgebraFunctor B S hS X)
      (boundedQuasicoherentAlgebraInclusion B S hS X)
  · intro h
    exact Functor.Full.of_comp_faithful_iso
      (eqToIso (boundedPushforwardAlgebraFunctor_comp_ι B S hS X))

/-- The direct-image functor
`f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the quasi-coherent `𝒪_X`-algebras
*whose sections at every étale chart of `X` are fewer than the big fppf site's cutoff* is an
equivalence exactly when the unrestricted direct-image functor is full, is faithful, and
reaches every quasi-coherent algebra satisfying that size condition. -/
theorem isEquivalence_boundedPushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).IsEquivalence ↔
      ((quasicoherentPushforwardAlgebraFunctor B S hS X).Full ∧
        (quasicoherentPushforwardAlgebraFunctor B S hS X).Faithful ∧
        ∀ A : QuasicoherentAlgebra B S hS X, AlgebraSheaf.SectionsBelowCutoff B S hS A.obj →
          (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A) := by
  refine ⟨fun h => ?_, fun ⟨hfull, hfaith, hsurj⟩ => ?_⟩
  · have := h
    exact ⟨(full_boundedPushforwardAlgebraFunctor_iff B S hS X).1 inferInstance,
      (faithful_boundedPushforwardAlgebraFunctor_iff B S hS X).1 inferInstance,
      (essSurj_boundedPushforwardAlgebraFunctor_iff B S hS).1 inferInstance⟩
  · have := (full_boundedPushforwardAlgebraFunctor_iff B S hS X).2 hfull
    have := (faithful_boundedPushforwardAlgebraFunctor_iff B S hS X).2 hfaith
    have := (essSurj_boundedPushforwardAlgebraFunctor_iff B S hS).2 hsurj
    exact { }

/-! ### Full faithfulness, reduced to the direct-image map of a morphism over `X` -/

/-- The direct-image functor is faithful exactly when `AlgebraicGeometry.Space.pushforwardRingMap`
is injective on the morphisms over `X` between objects affine over `X`. -/
theorem faithful_affinePushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).Faithful ↔
      ∀ (Y Z : AffineOver B S hS X) (f g : Y.obj ⟶ Z.obj),
        pushforwardRingMap B S hS f = pushforwardRingMap B S hS g → f = g := by
  constructor
  · intro h Y Z f g e
    have hop : (ObjectProperty.homMk f : Y ⟶ Z).op = (ObjectProperty.homMk g : Y ⟶ Z).op :=
      h.map_injective (ObjectProperty.hom_ext _ (AlgebraSheaf.Hom.ext e))
    exact congrArg (fun m : Y ⟶ Z => m.hom) (Quiver.Hom.op_inj hop)
  · intro h
    constructor
    intro Yop Zop m n e
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (h Zop.unop Yop.unop _ _ ?_))
    exact congrArg
      (fun k : pushforwardAlgebra B S hS Yop.unop.obj ⟶ pushforwardAlgebra B S hS Zop.unop.obj =>
        k.right)
      (congrArg
        (fun k : (quasicoherentPushforwardAlgebraFunctor B S hS X).obj Yop ⟶
            (quasicoherentPushforwardAlgebraFunctor B S hS X).obj Zop => k.hom) e)

/-- The direct-image functor is full exactly when `AlgebraicGeometry.Space.pushforwardAlgebraMap`
is surjective onto the morphisms of direct-image algebras. -/
theorem full_affinePushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).Full ↔
      ∀ (Y Z : AffineOver B S hS X)
        (φ : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y.obj),
        ∃ f : Y.obj ⟶ Z.obj, pushforwardAlgebraMap B S hS f = φ := by
  constructor
  · intro h Y Z φ
    obtain ⟨m, hm⟩ := h.map_surjective
      (ObjectProperty.homMk φ : (quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Z) ⟶
        (quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Y))
    exact ⟨m.unop.hom, congrArg
      (fun k : (quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Z) ⟶
          (quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Y) => k.hom) hm⟩
  · intro h
    constructor
    intro Yop Zop ψ
    obtain ⟨f, hf⟩ := h Zop.unop Yop.unop ψ.hom
    exact ⟨(ObjectProperty.homMk f : Zop.unop ⟶ Yop.unop).op, ObjectProperty.hom_ext _ hf⟩

/-- The direct-image functor `f ↦ f_* 𝒪_Y` into the quasi-coherent `𝒪_X`-algebras whose sections at
every étale chart of `X` are fewer than the big fppf site's cutoff is an equivalence exactly when

* for all `Y`, `Z` affine over `X` the map `f ↦ f_* : (Y ⟶ Z) → (Z_* 𝒪_Z ⟶ Y_* 𝒪_Y)` on
  morphisms over `X` is bijective, and
* every quasi-coherent `𝒪_X`-algebra satisfying the size condition is a direct image. -/
theorem isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective
    (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).IsEquivalence ↔
      ((∀ Y Z : AffineOver B S hS X,
          Function.Bijective
            (fun f : Y.obj ⟶ Z.obj => pushforwardAlgebraMap B S hS f)) ∧
        ∀ A : QuasicoherentAlgebra B S hS X, AlgebraSheaf.SectionsBelowCutoff B S hS A.obj →
          (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A) := by
  rw [isEquivalence_boundedPushforwardAlgebraFunctor_iff]
  constructor
  · rintro ⟨hfull, hfaith, hsurj⟩
    refine ⟨fun Y Z => ⟨fun f g e => ?_, fun φ => ?_⟩, hsurj⟩
    · exact (faithful_affinePushforwardAlgebraFunctor_iff B S hS X).1 hfaith Y Z f g
        (congrArg
          (fun k : pushforwardAlgebra B S hS Z.obj ⟶ pushforwardAlgebra B S hS Y.obj =>
            k.right) e)
    · exact (full_affinePushforwardAlgebraFunctor_iff B S hS X).1 hfull Y Z φ
  · rintro ⟨hbij, hsurj⟩
    refine ⟨(full_affinePushforwardAlgebraFunctor_iff B S hS X).2
        fun Y Z φ => (hbij Y Z).2 φ, ?_, hsurj⟩
    exact (faithful_affinePushforwardAlgebraFunctor_iff B S hS X).2
      fun Y Z f g e => (hbij Y Z).1 (AlgebraSheaf.Hom.ext e)

/-! ### The bounded anti-equivalence as a hypothesis structure -/

/-- The inclusion of the bounded quasi-coherent algebras on `X` into all sheaves of commutative
`𝒪_X`-algebras. -/
abbrev boundedAlgebraSheafInclusion (X : AlgebraicSpaces B S hS) :
    BoundedQuasicoherentAlgebra B S hS X ⥤ AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  boundedQuasicoherentAlgebraInclusion B S hS X ⋙ quasicoherentAlgebraInclusion B S hS X

/-- The data of an anti-equivalence between the algebraic spaces affine over `X` and the
quasi-coherent `𝒪_X`-algebras *whose sections at every étale chart of `X` are fewer than the big
fppf site's cutoff*, naturally identified with direct image. -/
structure BoundedAffineAlgebraAntiEquivalence where
  /-- The anti-equivalence over each algebraic space. -/
  equivalence : ∀ X : AlgebraicSpaces B S hS,
    (AffineOver B S hS X)ᵒᵖ ≌ BoundedQuasicoherentAlgebra B S hS X
  /-- Contravariant direct image of structure sheaves. -/
  pushforward : ∀ X : AlgebraicSpaces B S hS,
    (AffineOver B S hS X)ᵒᵖ ⥤ BoundedQuasicoherentAlgebra B S hS X
  /-- Its value on an affine morphism is that morphism's pushed-forward structure sheaf. -/
  pushforward_obj : ∀ (X : AlgebraicSpaces B S hS) (Y : AffineOver B S hS X),
    (boundedAlgebraSheafInclusion B S hS X).obj ((pushforward X).obj (.op Y)) ≅
      pushforwardAlgebra B S hS Y.obj
  /-- The action on morphisms is the canonical map on direct-image rings. -/
  pushforward_map : ∀ (X : AlgebraicSpaces B S hS) {Y Z : AffineOver B S hS X} (f : Y ⟶ Z),
    ((pushforward_obj X Z).inv ≫
      (boundedAlgebraSheafInclusion B S hS X).map ((pushforward X).map f.op) ≫
      (pushforward_obj X Y).hom).right =
      pushforwardRingMap B S hS f.hom
  /-- The anti-equivalence is naturally the direct-image functor. -/
  pushforwardIso : ∀ X : AlgebraicSpaces B S hS,
    (equivalence X).functor ≅ pushforward X

variable {B S hS}

/-- Given a bounded anti-equivalence, every quasi-coherent `𝒪_X`-algebra whose sections at every
étale chart of `X` are fewer than the cutoff is isomorphic to `f_* 𝒪_Y` for some algebraic space
`Y` affine over `X`. -/
theorem essImage_affinePushforwardAlgebraFunctor_of_bounded
    (E : BoundedAffineAlgebraAntiEquivalence B S hS) {X : AlgebraicSpaces B S hS}
    (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A := by
  set Ab : BoundedQuasicoherentAlgebra B S hS X := ⟨A, hA⟩ with hAb
  set Yop : (AffineOver B S hS X)ᵒᵖ := (E.equivalence X).inverse.obj Ab with hYop
  have i1 : Ab ≅ (E.pushforward X).obj Yop :=
    ((E.equivalence X).counitIso.app Ab).symm ≪≫ (E.pushforwardIso X).app Yop
  have i2 : (quasicoherentAlgebraInclusion B S hS X).obj A ≅
      pushforwardAlgebra B S hS Yop.unop.obj :=
    (boundedAlgebraSheafInclusion B S hS X).mapIso i1 ≪≫ E.pushforward_obj X Yop.unop
  exact ⟨Yop, ⟨((quasicoherentAlgebraInclusion B S hS X).preimageIso i2).symm⟩⟩

/-- A bounded anti-equivalence makes the bounded direct-image functor essentially surjective. -/
theorem essSurj_boundedPushforwardAlgebraFunctor_of
    (E : BoundedAffineAlgebraAntiEquivalence B S hS) (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).EssSurj :=
  (essSurj_boundedPushforwardAlgebraFunctor_iff B S hS).2
    fun A hA => essImage_affinePushforwardAlgebraFunctor_of_bounded E A hA

/-- The bounded anti-equivalence given by the bounded direct-image functor when it is an
equivalence, with its `pushforward` field the functor itself and both identifications the
identity. -/
def boundedAffineAlgebraAntiEquivalenceOfIsEquivalence
    (h : ∀ X : AlgebraicSpaces B S hS,
      (boundedPushforwardAlgebraFunctor B S hS X).IsEquivalence) :
    BoundedAffineAlgebraAntiEquivalence B S hS where
  equivalence X := haveI := h X; (boundedPushforwardAlgebraFunctor B S hS X).asEquivalence
  pushforward X := boundedPushforwardAlgebraFunctor B S hS X
  pushforward_obj X Y := Iso.refl ((boundedAlgebraSheafInclusion B S hS X).obj
    ((boundedPushforwardAlgebraFunctor B S hS X).obj (op Y)))
  pushforward_map := by
    intro X Y Z f
    change (𝟙 ((boundedAlgebraSheafInclusion B S hS X).obj
          ((boundedPushforwardAlgebraFunctor B S hS X).obj (op Z))) ≫
        (boundedAlgebraSheafInclusion B S hS X).map
          ((boundedPushforwardAlgebraFunctor B S hS X).map f.op) ≫
        𝟙 ((boundedAlgebraSheafInclusion B S hS X).obj
          ((boundedPushforwardAlgebraFunctor B S hS X).obj (op Y)))).right =
      pushforwardRingMap B S hS f.hom
    rw [Category.id_comp, Category.comp_id]
    rfl
  pushforwardIso X := haveI := h X; Iso.refl _

/-- The relative spectrum `\underline{Spec}_X(A)` of a quasi-coherent `𝒪_X`-algebra on an algebraic
space `X`, as an algebraic space affine over `X`: the value on `A` of the inverse of a given
*bounded* anti-equivalence of Stacks 081V. -/
def BoundedAffineAlgebraAntiEquivalence.relativeSpec
    (E : BoundedAffineAlgebraAntiEquivalence B S hS) {X : AlgebraicSpaces B S hS}
    (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) : AffineOver B S hS X :=
  ((E.equivalence X).inverse.obj ⟨A, hA⟩).unop

/-- The direct image of the structure sheaf of the relative spectrum of a bounded quasi-coherent
algebra is that algebra: the counit of the bounded anti-equivalence, read through its
identification with direct image. -/
def BoundedAffineAlgebraAntiEquivalence.relativeSpecPushforwardIso
    (E : BoundedAffineAlgebraAntiEquivalence B S hS) {X : AlgebraicSpaces B S hS}
    (A : QuasicoherentAlgebra B S hS X)
    (hA : AlgebraSheaf.SectionsBelowCutoff B S hS A.obj) :
    pushforwardAlgebra B S hS (E.relativeSpec A hA).obj ≅ A.obj :=
  (E.pushforward_obj X (E.relativeSpec A hA)).symm ≪≫
    (boundedAlgebraSheafInclusion B S hS X).mapIso
      (((E.pushforwardIso X).app (op (E.relativeSpec A hA))).symm ≪≫
        (E.equivalence X).counitIso.app ⟨A, hA⟩)

end AlgebraicGeometry.Space

end
