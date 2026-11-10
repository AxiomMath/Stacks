module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSource
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence

/-!
# The identifications of the kernels with affine source, read through the integral transform

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with the diagonal of `X` over
`R` affine, and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting with
arbitrary direct sums.  For every morphism `f : X' ⟶ X` of schemes over `R` with `X'` affine,
`StacksFrontier/AlgebraicGeometry/FunctorsAndMorphisms/IntegralTransformQcoh/AffineSource.lean`
attaches to `f` a quasi-coherent kernel `K_f` on `X' ×_R Y`, a comparison `F ∘ f_* ≅ F_{K_f}`,
and for a further morphism `g : X'' ⟶ X'` with `X''` affine the identification
`(g × id_Y)^*K_f ≅ K_{g ≫ f}` of Tag 0FZF.

This file reads those identifications through the integral transform.  That is the shape in
which they can be compared with one another, since the functor of Tag 0FZD from quasi-coherent
kernels on an affine source to right exact linear direct-sum-preserving functors is fully
faithful:  an identity between morphisms of kernels is an identity between the corresponding
morphisms of integral transforms, and conversely.

## Main definitions

* `AlgebraicGeometry.sourceChangeKernelMap` is the inverse image along `f × id_Y` of a morphism
  of quasi-coherent kernels, with its source and target spelled by
  `AlgebraicGeometry.sourceChangeKernel`.

## Main results

* `AlgebraicGeometry.kernel_hom_ext`: two morphisms of quasi-coherent kernels on an affine
  source with the same integral transform are equal.  This is faithfulness of the functor of
  Tag 0FZD, in the form in which an identity of morphisms of kernels is proved.
* `AlgebraicGeometry.map_kernelIsoOfIntegralTransformIso`: the integral transform of the
  isomorphism of kernels attached to an isomorphism of integral transforms is that isomorphism.
* `AlgebraicGeometry.map_sourceChangeKernelMap`: **affine change of source of Tag 0FZF is
  natural in the kernel**, in the form that computes the integral transform of the inverse image
  of a morphism of kernels.
* `AlgebraicGeometry.map_affineSourceKernelSourceChangeIso` and
  `AlgebraicGeometry.sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso`: the
  identification `(g × id_Y)^*K_f ≅ K_{g ≫ f}` of the kernels with affine source, read through
  the integral transform, as a composite and as a commuting triangle.
* `AlgebraicGeometry.quasicoherentPushforwardComp_hom_app` and
  `AlgebraicGeometry.associator_hom_app`: the direct image on quasi-coherent modules composes on
  the nose, so the comparison of the two composite direct images and the associator of three
  functors are identities at every object.
* `AlgebraicGeometry.whiskerRight_eqToIso_quasicoherentPushforward_integralTransform_app` and
  `AlgebraicGeometry.integralTransform_map_eqToIso_hom_app`: the same for the comparison that
  appears in the pseudo-functoriality of Tag 0FZF, applied to an integral transform.
* `AlgebraicGeometry.map_eqToIso_quasicoherentPushforward_hom_app`: any functor out of the
  quasi-coherent modules carries the comparison of the two spellings of a composite direct image
  to the identity.
* `AlgebraicGeometry.whiskerRight_quasicoherentPushforwardComp_hom_app` and
  `AlgebraicGeometry.whiskerRight_quasicoherentPushforwardComp_comp_app`: the comparison of the
  direct images along a composite, whiskered by any functor out of the quasi-coherent modules on
  the target, is the identity at every quasi-coherent module, and is therefore absorbed by
  whatever natural transformation follows it.
* `AlgebraicGeometry.quasicoherentPushforwardComp_hom_eq_eqToIso_inv`: the comparison of the two
  composite direct images is the transport along the equality of functors of
  `AlgebraicGeometry.quasicoherentPushforward_eq_comp`.
* `AlgebraicGeometry.affineSourceKernelIso_hom_comp_map_eqToHom`: the two bracketings of a
  triple composite with affine sources give the same kernel, and the comparison between them is
  the identity.
* `AlgebraicGeometry.whiskerLeft_affineSourceKernelTriangle`: the commuting triangle of the
  kernels with affine source, after a further direct image, with the two whiskerings on the left
  merged into one.
* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp'`:
  pseudo-functoriality of affine change of source of Tag 0FZF, at the kernel attached to a
  morphism with affine source.
* `AlgebraicGeometry.whiskerLeft_comp_whiskerRight_coherence`: the coherence of an iterated
  whiskering whose four comparisons are transports along equalities of functors.  This is the
  cocycle condition stripped of all geometry.
* `AlgebraicGeometry.pushforwardComp_coherence`: the degenerate coherence of the composite direct
  image for a triple composite, which is what the cocycle condition reduces to.
* `AlgebraicGeometry.affineSourceKernelSourceChangeIso_comp`: **the cocycle condition of
  Tag 0GPA.**  For a third morphism `h` with affine source, the identification of the iterated
  inverse image of `K_f` with the kernel of the triple composite does not depend on whether the
  source is changed in one step or in two.

## Implementation notes

The cocycle condition is proved in three steps, and the split is forced by the per-declaration
heartbeat budget rather than by mathematics.

`AlgebraicGeometry.kernel_hom_ext` turns the identity of morphisms of kernels into one of
integral transforms, and `AlgebraicGeometry.map_sourceChangeKernelMap`,
`AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp'`,
`AlgebraicGeometry.sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso` (whose
`reassoc` form is what the rewrite uses),
`AlgebraicGeometry.whiskerLeft_affineSourceKernelTriangle` and
`AlgebraicGeometry.affineSourceKernelIso_hom_comp_map_eqToHom` reduce it to
`AlgebraicGeometry.pushforwardComp_coherence`:  an identity each of whose factors other than the
comparison `F ∘ f_* ≅ F_{K_f}` is the identity at every quasi-coherent module.

That identity is *not* proved by recognising those factors as identities one at a time.  The
reason is the budget.  The comparison `F ∘ f_* ≅ F_{K_f}` occurs on the two sides at two objects
that are definitionally equal but differently spelled -- `(h ≫ g)_*M` against `g_*(h_*M)`, since
`AlgebraicGeometry.quasicoherentPushforward` of a composite is the composite of the direct images
one quasi-coherent module at a time -- and that identification, for an arbitrary natural
transformation out of an arbitrary functor, is `rfl` but costs about a second.  A proof that
cancels the factors one at a time asks for it several times:  once to bring the two components
together, once to recognise the comparison of the two spellings as an identity, once to cancel
`F ∘ (g ≫ f)_* ≅ F_{K_{g ≫ f}}` against its inverse.  Two or three in one declaration exceed the
200000 heartbeats, and splitting them into separate declarations does not help, since the
identification has to be re-established on each side of the split.

What works is to remove the definitional identifications rather than pay for them.  Each
`AlgebraicGeometry.quasicoherentPushforwardComp` factor is replaced by the transport along the
corresponding instance of `AlgebraicGeometry.quasicoherentPushforward_eq_comp` -- the conversion
is `AlgebraicGeometry.quasicoherentPushforwardComp_hom_eq_eqToIso_inv`, and it is where the
identification is paid, once -- after which every comparison in the identity is an `eqToIso` of
an *equality of functors*.  The identity in that form is
`AlgebraicGeometry.whiskerLeft_comp_whiskerRight_coherence`, which has no geometry in it at all:
`subst` on the equalities of functors makes its two sides syntactically equal, and the kernel is
never asked to identify a direct image along a composite with a composite of direct images.

The transport along `Category.assoc h g f` in the statement of
`AlgebraicGeometry.affineSourceKernelSourceChangeIso_comp` is an identity morphism, by
`AlgebraicGeometry.affineSourceKernelIso_hom_comp_map_eqToHom`, but it cannot be dropped:  the
two bracketings of the triple composite are definitionally equal only at default transparency,
and without the transport the equation's type carries a coercion that no tactic can see past.
The local `implicit_reducible` attributes of the sections below are what make composition in
`Over (Spec R)` reduce at the `implicit` transparency at which a rewrite checks its motive; the
price of them is that `Over.Hom.left h` has to be written out, since dot notation stops
resolving.

## What is not here

The gluing of the kernels with affine source into a single quasi-coherent kernel on `X ×_R Y`,
and the comparison of `F` with its integral transform, are the other clauses of Tag 0GPA and are
not here.  This file provides the cocycle condition they consume.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] isOpenImmersion_over_comp_left

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

section Faithful

variable (R : Type u) [CommRing R] (Z Y : Over (Spec (.of R))) [IsAffine Z.left]

/-- **Two morphisms of quasi-coherent kernels on an affine source with the same integral
transform are equal.**  This is faithfulness of the functor of Tag 0FZD. -/
theorem kernel_hom_ext {K L : Scheme.QuasicoherentModules (pullback Z.hom Y.hom)} {a b : K ⟶ L}
    (h : (integralTransformQcohFunctor R Z Y).map a =
      (integralTransformQcohFunctor R Z Y).map b) : a = b := by
  have : (integralTransformQcohFunctorLift R Z Y).Faithful :=
    faithful_integralTransformQcohFunctorLift R Z Y
  refine (integralTransformQcohFunctorLift R Z Y).map_injective ?_
  exact (ObjectProperty.ι (rightExactLinearCoproductFunctor R Z Y)).map_injective h

/-- The integral transform of the isomorphism of kernels attached by
`AlgebraicGeometry.kernelIsoOfIntegralTransformIso` to an isomorphism of integral transforms is
that isomorphism. -/
theorem map_kernelIsoOfIntegralTransformIso
    {K L : Scheme.QuasicoherentModules (pullback Z.hom Y.hom)}
    (e : quasicoherentIntegralTransform R Z Y K ≅ quasicoherentIntegralTransform R Z Y L) :
    (integralTransformQcohFunctor R Z Y).map
        (kernelIsoOfIntegralTransformIso R Z Y e).hom = e.hom := by
  have : (integralTransformQcohFunctorLift R Z Y).Full :=
    full_integralTransformQcohFunctorLift R Z Y
  have : (integralTransformQcohFunctorLift R Z Y).Faithful :=
    faithful_integralTransformQcohFunctorLift R Z Y
  have h := (Functor.FullyFaithful.ofFullyFaithful
      (integralTransformQcohFunctorLift R Z Y)).map_preimage
    (ObjectProperty.isoMk (rightExactLinearCoproductFunctor R Z Y) e).hom
  exact congrArg
    (fun φ => (ObjectProperty.ι (rightExactLinearCoproductFunctor R Z Y)).map φ) h

/-! ### The inverse image of a morphism of kernels -/

/-- The inverse image along `f × id_Y` of a morphism of quasi-coherent kernels, with its source
and target spelled by `AlgebraicGeometry.sourceChangeKernel`.  This is
`AlgebraicGeometry.sourceChangeKernelFunctor` on morphisms; the point of the separate name is
the spelling of the type, which lets a composite with the comparisons of Tag 0FZF be written
down without an identification of objects. -/
def sourceChangeKernelMap (R : Type u) [CommRing R] (Z Z' W : Over (Spec (.of R)))
    (a : Z' ⟶ Z) {K L : Scheme.QuasicoherentModules (pullback Z.hom W.hom)} (φ : K ⟶ L) :
    sourceChangeKernel R Z Z' W a K ⟶ sourceChangeKernel R Z Z' W a L :=
  (sourceChangeKernelFunctor R Z Z' W a).map φ

/-- The inverse image of a morphism of kernels is inverse image on quasi-coherent modules along
the source-change morphism, which is the spelling the naturality of Tag 0FZF's comparison is
stated at. -/
theorem sourceChangeKernelMap_eq (R : Type u) [CommRing R] (Z Z' W : Over (Spec (.of R)))
    (a : Z' ⟶ Z) {K L : Scheme.QuasicoherentModules (pullback Z.hom W.hom)} (φ : K ⟶ L) :
    sourceChangeKernelMap R Z Z' W a φ =
      (quasicoherentPullback (sourceChangeMap R Z Z' W a)).map φ := rfl

end Faithful

/-! ### Naturality of affine change of source in the kernel -/

section Naturality

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

variable (R : Type u) [CommRing R] (X₂ X₃ Y : Over (Spec (.of R)))
  [IsAffine X₂.left] [IsAffine X₃.left]

/-- **Affine change of source of Tag 0FZF is natural in the kernel**, in the form that computes
the integral transform of the inverse image of a morphism of kernels. -/
theorem map_sourceChangeKernelMap (h : X₃ ⟶ X₂)
    {K L : Scheme.QuasicoherentModules (pullback X₂.hom Y.hom)} (φ : K ⟶ L) :
    (integralTransformQcohFunctor R X₃ Y).map (sourceChangeKernelMap R X₂ X₃ Y h φ) =
      (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h K).inv ≫
        Functor.whiskerLeft (quasicoherentPushforward h.left)
            ((integralTransformQcohFunctor R X₂ Y).map φ) ≫
          (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h L).hom := by
  have hnat := quasicoherentIntegralTransformSourceChangeIso_naturality R X₂ X₃ Y h K L φ
  have e0 : (integralTransformQcohFunctor R X₃ Y).map
        ((quasicoherentPullback (sourceChangeMap R X₂ X₃ Y h)).map φ) =
      (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h K).inv ≫
        Functor.whiskerLeft (quasicoherentPushforward h.left)
            ((integralTransformQcohFunctor R X₂ Y).map φ) ≫
          (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h L).hom := by
    rw [hnat]
    exact (Iso.inv_hom_id_assoc _ _).symm
  exact e0

end Naturality

/-! ### The degenerate comparisons -/

section Degenerate

/-- The comparison of the direct images along a composite, on quasi-coherent modules, is the
identity at every quasi-coherent module:  the direct image on quasi-coherent modules composes
on the nose. -/
theorem quasicoherentPushforwardComp_hom_app {Z Z' Z'' : Scheme.{u}} (a : Z'' ⟶ Z')
    (b : Z' ⟶ Z) [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    [QuasiCompact (a ≫ b)] [QuasiSeparated (a ≫ b)]
    (M : Scheme.QuasicoherentModules Z'') :
    (quasicoherentPushforwardComp a b).hom.app M = 𝟙 _ := rfl

/-- The comparison of the direct images along a composite, whiskered by *any* functor out of the
quasi-coherent modules on the target, is the identity at every quasi-coherent module.  This is
`AlgebraicGeometry.quasicoherentPushforwardComp_hom_app` in the shape in which it occurs in a
coherence diagram. -/
theorem whiskerRight_quasicoherentPushforwardComp_hom_app {Z Z' Z'' : Scheme.{u}} (a : Z'' ⟶ Z')
    (b : Z' ⟶ Z) [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    [QuasiCompact (a ≫ b)] [QuasiSeparated (a ≫ b)] {C : Type*} [Category C]
    (G : Scheme.QuasicoherentModules Z ⥤ C) (M : Scheme.QuasicoherentModules Z'') :
    (Functor.whiskerRight (quasicoherentPushforwardComp a b).hom G).app M = 𝟙 _ :=
  (Functor.whiskerRight_app _ _ _).trans
    ((congrArg G.map (quasicoherentPushforwardComp_hom_app a b M)).trans (G.map_id _))

/-- `AlgebraicGeometry.whiskerRight_quasicoherentPushforwardComp_hom_app` in the shape it is used
in:  the comparison of the direct images along a composite is absorbed by whatever natural
transformation follows it. -/
theorem whiskerRight_quasicoherentPushforwardComp_comp_app {Z Z' Z'' : Scheme.{u}} (a : Z'' ⟶ Z')
    (b : Z' ⟶ Z) [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    [QuasiCompact (a ≫ b)] [QuasiSeparated (a ≫ b)] {C : Type*} [Category C]
    (G : Scheme.QuasicoherentModules Z ⥤ C)
    {Q : Scheme.QuasicoherentModules Z'' ⥤ C}
    (ψ : quasicoherentPushforward (a ≫ b) ⋙ G ⟶ Q) (M : Scheme.QuasicoherentModules Z'') :
    (Functor.whiskerRight (quasicoherentPushforwardComp a b).hom G ≫ ψ).app M = ψ.app M :=
  (NatTrans.comp_app _ _ _).trans
    ((congrArg (fun z => z ≫ ψ.app M)
      (whiskerRight_quasicoherentPushforwardComp_hom_app a b G M)).trans (Category.id_comp _))

/-- The functor of kernels of Tag 0FZD sends a kernel to its integral transform. -/
theorem integralTransformQcohFunctor_obj (R : Type u) [CommRing R]
    (Z W : Over (Spec (.of R))) [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    (K : Scheme.QuasicoherentModules (pullback Z.hom W.hom)) :
    (integralTransformQcohFunctor R Z W).obj K = quasicoherentIntegralTransform R Z W K := rfl

/-- The associator of three functors is the identity at every object. -/
theorem associator_hom_app {C D E E' : Type*} [Category C] [Category D] [Category E]
    [Category E'] (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ E') (M : C) :
    (G.associator H I).hom.app M = 𝟙 _ := rfl

/-- **The coherence of an iterated whiskering whose comparisons are transports.**  Let `S`, `T`,
`V` and `G` be functors, let `U` be a functor *equal* to `S ⋙ T`, let `W` be one equal to
`T ⋙ V`, and let `Z` be one equal both to `U ⋙ V` and to `S ⋙ W`.  Let `τ : P ⟶ V ⋙ G` and let
`ρ : W ⋙ G ≅ Q`.  Then whiskering `τ` by `U` in one step agrees with whiskering it by `T` and
then by `S`, up to the four comparisons -- provided each comparison is the transport along the
corresponding equality of functors.

This is the cocycle condition of Tag 0GPA stripped of all geometry.  The hypotheses are what make
it provable:  the comparisons are *propositional* transports, so `subst` on the equalities of
functors makes the two sides syntactically equal, and no definitional identification of a
composite direct image with a composite of direct images is ever asked for.  The identification
is paid once and for all, outside this lemma, when the equalities of functors are produced by
`AlgebraicGeometry.quasicoherentPushforward_eq_comp`. -/
theorem whiskerLeft_comp_whiskerRight_coherence {A B C D E : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category E] {S : A ⥤ B} {T : B ⥤ C} {V : C ⥤ D} {G : D ⥤ E}
    {U : A ⥤ C} {W : B ⥤ D} {Z : A ⥤ D} {P : C ⥤ E} {Q : B ⥤ E}
    (hU : U = S ⋙ T) (hW : W = T ⋙ V) (hZ : Z = U ⋙ V) (hZ' : Z = S ⋙ W)
    (τ : P ⟶ V ⋙ G) (ρ : W ⋙ G ≅ Q)
    {κ : U ⟶ S ⋙ T} (hκ : κ = (eqToIso hU).hom)
    {pc₁ : U ⋙ V ⟶ Z} (hpc₁ : pc₁ = (eqToIso hZ).inv)
    {pc₂ : T ⋙ V ⟶ W} (hpc₂ : pc₂ = (eqToIso hW).inv)
    {pc₃ : S ⋙ W ⟶ Z} (hpc₃ : pc₃ = (eqToIso hZ').inv) :
    Functor.whiskerLeft U τ ≫ Functor.whiskerRight pc₁ G =
      Functor.whiskerRight κ P ≫ (S.associator T P).hom ≫
        Functor.whiskerLeft S (Functor.whiskerLeft T τ ≫
            Functor.whiskerRight pc₂ G ≫ ρ.hom) ≫
          Functor.whiskerLeft S ρ.inv ≫ Functor.whiskerRight pc₃ G := by
  subst hκ hpc₁ hpc₂ hpc₃
  subst hU
  subst hZ
  subst hW
  -- The three substitutions leave `hZ' : (S ⋙ T) ⋙ V = S ⋙ T ⋙ V`, whose two sides are the
  -- same functor:  by proof irrelevance it is `rfl`, and its transport is the identity.
  have hr : hZ' = rfl := rfl
  subst hr
  refine NatTrans.ext (funext fun M => ?_)
  simp

variable (R : Type u) [CommRing R] (Y : Over (Spec (.of R)))

/-- A functor out of the quasi-coherent modules carries the comparison of the two spellings of a
composite direct image, at a module, to the identity. -/
private theorem map_eqToIso_quasicoherentPushforward_hom_app_aux {C : Type*} [Category C]
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂) (P : Scheme.QuasicoherentModules X₁.left ⥤ C)
    (M : Scheme.QuasicoherentModules X₃.left) :
    P.map ((eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom.app M) = 𝟙 _ := by
  rw [eqToIso.hom, eqToHom_app]
  exact (congrArg P.map (eqToHom_refl _ _)).trans (P.map_id _)

/-- The comparison of the direct images along a composite of affine morphisms, applied to the
integral transform of a quasi-coherent kernel, is the identity at every quasi-coherent
module. -/
theorem whiskerRight_eqToIso_quasicoherentPushforward_integralTransform_app
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom))
    (M : Scheme.QuasicoherentModules X₃.left) :
    (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom
        (quasicoherentIntegralTransform R X₁ Y K)).app M = 𝟙 _ :=
  (Functor.whiskerRight_app _ _ _).trans
    (map_eqToIso_quasicoherentPushforward_hom_app_aux R g h _ M)

/-- `AlgebraicGeometry.whiskerRight_eqToIso_quasicoherentPushforward_integralTransform_app` with
the whiskering already evaluated at the module, which is the shape it is used in. -/
theorem integralTransform_map_eqToIso_hom_app
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom))
    (M : Scheme.QuasicoherentModules X₃.left) :
    (quasicoherentIntegralTransform R X₁ Y K).map
        ((eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom.app M) = 𝟙 _ :=
  map_eqToIso_quasicoherentPushforward_hom_app_aux R g h _ M

/-- The comparison of the direct images along the two spellings of a composite of affine
morphisms is carried to the identity by *any* functor out of the quasi-coherent modules on the
source:  the comparison is a transport along an equality of functors whose two sides agree at
every quasi-coherent module.  This is
`AlgebraicGeometry.integralTransform_map_eqToIso_hom_app` with the integral transform replaced by
an arbitrary functor, which is the generality the triple-overlap comparison needs. -/
theorem map_eqToIso_quasicoherentPushforward_hom_app {C : Type*} [Category C]
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂) (P : Scheme.QuasicoherentModules X₁.left ⥤ C)
    (M : Scheme.QuasicoherentModules X₃.left) :
    P.map ((eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom.app M) = 𝟙 _ :=
  map_eqToIso_quasicoherentPushforward_hom_app_aux R g h P M

end Degenerate

/-! ### The cocycle condition -/

section Cocycle

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_left_of_isAffine_left

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

/-- The identification of Tag 0FZF of the kernels attached to `f` and to `g ≫ f`, read through
the integral transform:  it is the composite of the inverse of affine change of source along
`g`, the comparison of `F ∘ f_*` with the integral transform of the kernel of `f`, the
composition of the two direct images, and the comparison at `g ≫ f`. -/
theorem map_affineSourceKernelSourceChangeIso
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)] :
    (integralTransformQcohFunctor R X₂ Y).map
        (affineSourceKernelSourceChangeIso R X Y F hF f g).hom =
      (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
          (affineSourceKernel R X Y F hF f)).inv ≫
        Functor.whiskerLeft (quasicoherentPushforward g.left)
          (affineSourceKernelIso R X Y F hF f).inv ≫
        Functor.whiskerRight (quasicoherentPushforwardComp g.left f.left).hom F ≫
        (affineSourceKernelIso R X Y F hF (g ≫ f)).hom :=
  map_kernelIsoOfIntegralTransformIso R X₂ Y _

/-- Pseudo-functoriality of the source-change isomorphism of Tag 0FZF, at the kernel attached to
a morphism with affine source and with the instances of the ambient context. -/
theorem quasicoherentIntegralTransformSourceChangeIso_comp'
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    (K : Scheme.QuasicoherentModules (pullback X₁.hom Y.hom)) :
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₃ Y (h ≫ g) K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom
          (quasicoherentIntegralTransform R X₁ Y K) ≫
        ((quasicoherentPushforward h.left).associator (quasicoherentPushforward g.left)
              (quasicoherentIntegralTransform R X₁ Y K)).hom ≫
          Functor.whiskerLeft (quasicoherentPushforward h.left)
              (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X₂ X₃ Y h
                (sourceChangeKernel R X₁ X₂ Y g K)).hom ≫
              (integralTransformQcohFunctor R X₃ Y).map
                (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h K).inv :=
  quasicoherentIntegralTransformSourceChangeIso_comp R X₁ X₂ X₃ Y g h K

/-- **The identification of the kernels with affine source, in triangle form.**  The comparison
`AlgebraicGeometry.affineSourceKernelSourceChangeIso` of the inverse image along `g` of the
kernel of `f` with the kernel of `g ≫ f` is the unique morphism of kernels whose integral
transform makes the triangle formed by affine change of source of Tag 0FZF and the two
comparisons `F ∘ f_* ≅ F_{K_f}` and `F ∘ (g ≫ f)_* ≅ F_{K_{g ≫ f}}` commute. -/
@[reassoc]
theorem sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)] :
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
          (affineSourceKernel R X Y F hF f)).hom ≫
        (integralTransformQcohFunctor R X₂ Y).map
          (affineSourceKernelSourceChangeIso R X Y F hF f g).hom =
      Functor.whiskerLeft (quasicoherentPushforward g.left)
          (affineSourceKernelIso R X Y F hF f).inv ≫
        Functor.whiskerRight (quasicoherentPushforwardComp g.left f.left).hom F ≫
          (affineSourceKernelIso R X Y F hF (g ≫ f)).hom := by
  simp only [map_affineSourceKernelSourceChangeIso, Iso.hom_inv_id_assoc]

end Cocycle

/-! ### Reassociating the triple composite -/

section Reassociation

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_left_of_isAffine_left

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful
  CategoryTheory.instCategoryOver CategoryTheory.commaCategory

/-- **The comparison of the two composite direct images is the comparison of the two spellings of
the composite.**  Both are the identity at every quasi-coherent module, so the normalisation of
`AlgebraicGeometry.quasicoherentPushforwardComp` agrees with the transport along the equality of
functors of `AlgebraicGeometry.quasicoherentPushforward_eq_comp`.  The point of the second
spelling is that its source and target are written with the composite `g ≫ f` of morphisms over
`R` already formed, which is the shape in which the comparison can be cancelled against the
kernels attached to a morphism with affine source. -/
theorem quasicoherentPushforwardComp_hom_eq_eqToIso_inv
    {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) :
    (quasicoherentPushforwardComp (Over.Hom.left g) (Over.Hom.left f)).hom =
      (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).inv := by
  refine NatTrans.ext (funext fun M => ?_)
  rw [quasicoherentPushforwardComp_hom_app, eqToIso.inv, eqToHom_app]
  exact (eqToHom_refl _ _).symm

/-- **The two bracketings of a triple composite give the same kernel.**  Associativity in
`Over (Spec R)` holds on the nose, so the comparison of the kernels attached to `(h ≫ g) ≫ f`
and to `h ≫ g ≫ f` is an identity and cancels against the comparison
`F ∘ ((h ≫ g) ≫ f)_* ≅ F_{K_{(h ≫ g) ≫ f}}`, leaving the comparison at `h ≫ g ≫ f`.

The transport appears at all only to pin down a single spelling of the triple composite.  It has
to be pinned:  the two bracketings are definitionally equal, but only at default transparency,
and a statement in which both spellings occur carries a coercion that no rewriting tactic can
see past, since the motive of a rewrite is checked at `implicit` transparency. -/
theorem affineSourceKernelIso_hom_comp_map_eqToHom
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    [IsOpenImmersion (Over.Hom.left h)] :
    (affineSourceKernelIso R X Y F hF ((h ≫ g) ≫ f)).hom ≫
        (integralTransformQcohFunctor R X₃ Y).map
          (eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f))) =
      (affineSourceKernelIso R X Y F hF (h ≫ g ≫ f)).hom :=
  have h0 : (integralTransformQcohFunctor R X₃ Y).map
      (eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f))) = 𝟙 _ :=
    (congrArg (integralTransformQcohFunctor R X₃ Y).map
      (show eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f)) = 𝟙 _ from
        rfl)).trans
      ((integralTransformQcohFunctor R X₃ Y).map_id _)
  (congrArg (fun t => (affineSourceKernelIso R X Y F hF ((h ≫ g) ≫ f)).hom ≫ t) h0).trans
    (Category.comp_id _)

/-- **The identification of the kernels with affine source, after a further direct image.**  The
commuting triangle of
`AlgebraicGeometry.sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso`, with the
direct image along a third morphism `h` with affine source applied to all of it.  The two
whiskerings on the left are merged into one, which is the shape the triple-overlap comparison
needs:  in that comparison the two factors arrive separated by the pseudo-functoriality of
Tag 0FZF, and they have to be recombined before the triangle can be used. -/
@[reassoc]
theorem whiskerLeft_affineSourceKernelTriangle
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    [IsOpenImmersion (Over.Hom.left h)] :
    Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
          (quasicoherentIntegralTransformSourceChangeIso R X₁ X₂ Y g
            (affineSourceKernel R X Y F hF f)).hom ≫
        Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
          ((integralTransformQcohFunctor R X₂ Y).map
            (affineSourceKernelSourceChangeIso R X Y F hF f g).hom) =
      Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
        (Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left g))
            (affineSourceKernelIso R X Y F hF f).inv ≫
          Functor.whiskerRight (quasicoherentPushforwardComp (Over.Hom.left g)
              (Over.Hom.left f)).hom F ≫
            (affineSourceKernelIso R X Y F hF (g ≫ f)).hom) := by
  rw [← Functor.whiskerLeft_comp,
    sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso R X Y F hF f g]

/-- **The degenerate coherence of the composite direct image for a triple composite.**  Changing
the source of the kernel of `f` along `h ≫ g` in one step and changing it along `g` and then
along `h` differ only by comparisons that are the identity at every quasi-coherent module:  the
two spellings `(h ≫ g)_*` and `h_* ∘ g_*` of a composite direct image, the associator of three
functors, and the normalisation of `AlgebraicGeometry.quasicoherentPushforwardComp`.  This is
what the cocycle condition of Tag 0GPA reduces to once both of its sides have been rewritten by
the commuting triangle of
`AlgebraicGeometry.sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso` and by
pseudo-functoriality of affine change of source.

The proof replaces every occurrence of `AlgebraicGeometry.quasicoherentPushforwardComp` by the
transport along the corresponding instance of
`AlgebraicGeometry.quasicoherentPushforward_eq_comp`, using
`AlgebraicGeometry.quasicoherentPushforwardComp_hom_eq_eqToIso_inv`, and then appeals to
`AlgebraicGeometry.whiskerLeft_comp_whiskerRight_coherence`, where the identifications have
become propositional and are discharged by `subst`.  Nothing here asks the kernel to recognise a
direct image along a composite as a composite of direct images. -/
@[reassoc]
theorem pushforwardComp_coherence (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    [IsOpenImmersion (Over.Hom.left h)] :
    Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left (h ≫ g)))
          (affineSourceKernelIso R X Y F hF f).inv ≫
        Functor.whiskerRight (quasicoherentPushforwardComp (Over.Hom.left (h ≫ g))
          (Over.Hom.left f)).hom F =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp g h rfl)).hom
            (quasicoherentIntegralTransform R X₁ Y (affineSourceKernel R X Y F hF f)) ≫
        ((quasicoherentPushforward (Over.Hom.left h)).associator
              (quasicoherentPushforward (Over.Hom.left g))
              (quasicoherentIntegralTransform R X₁ Y (affineSourceKernel R X Y F hF f))).hom ≫
          Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
              (Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left g))
                  (affineSourceKernelIso R X Y F hF f).inv ≫
                Functor.whiskerRight (quasicoherentPushforwardComp (Over.Hom.left g)
                    (Over.Hom.left f)).hom F ≫
                  (affineSourceKernelIso R X Y F hF (g ≫ f)).hom) ≫
            Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left h))
                (affineSourceKernelIso R X Y F hF (g ≫ f)).inv ≫
              Functor.whiskerRight (quasicoherentPushforwardComp (Over.Hom.left h)
                  (Over.Hom.left (g ≫ f))).hom F :=
  whiskerLeft_comp_whiskerRight_coherence (quasicoherentPushforward_eq_comp g h rfl)
    (quasicoherentPushforward_eq_comp f g rfl) (quasicoherentPushforward_eq_comp f (h ≫ g) rfl)
    (quasicoherentPushforward_eq_comp (g ≫ f) h rfl)
    (affineSourceKernelIso R X Y F hF f).inv (affineSourceKernelIso R X Y F hF (g ≫ f)) rfl
    (quasicoherentPushforwardComp_hom_eq_eqToIso_inv R X f (h ≫ g))
    (quasicoherentPushforwardComp_hom_eq_eqToIso_inv R X f g)
    (quasicoherentPushforwardComp_hom_eq_eqToIso_inv R X (g ≫ f) h)

/-- **The cocycle condition of Tag 0GPA**, which the source leaves to the reader to spell out.
Let `f : X₁ ⟶ X`, `g : X₂ ⟶ X₁` and `h : X₃ ⟶ X₂` be morphisms of schemes over `R` with `X₁`,
`X₂` and `X₃` affine.  The identification
`AlgebraicGeometry.affineSourceKernelSourceChangeIso` of the inverse image of the kernel of `f`
with the kernel of `g ≫ f` is compatible with a further change of source along `h`:  changing the
source along `h ≫ g` in one step agrees with changing it along `g` and then along `h`, up to the
comparison `AlgebraicGeometry.sourceChangeKernelCompIso` of the two iterated inverse images.

Nothing is assumed beyond the data:  `X` is an arbitrary scheme over `R` whose diagonal is
affine, `Y` an arbitrary scheme over `R`, and `F` an arbitrary `R`-linear right exact functor
commuting with arbitrary direct sums.  This is the `trans` field a module glue datum for the
kernels with affine source asks for.

The transport along `Category.assoc h g f` pins the triple composite to one spelling.  It has to
be pinned:  the two bracketings are definitionally equal only at default transparency, and a
statement in which both spellings occur carries a coercion that no rewriting tactic can see past.
The transport is an identity morphism, and
`AlgebraicGeometry.affineSourceKernelIso_hom_comp_map_eqToHom` is what cancels it. -/
theorem affineSourceKernelSourceChangeIso_comp
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)
    {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left] [IsAffine X₂.left] [IsAffine X₃.left]
    (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    [IsOpenImmersion (Over.Hom.left f)] [IsOpenImmersion (Over.Hom.left g)]
    [IsOpenImmersion (Over.Hom.left h)] :
    (affineSourceKernelSourceChangeIso R X Y F hF f (h ≫ g)).hom ≫
        eqToHom (affineSourceKernel_congr R X Y F hF (Category.assoc h g f)) =
      (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h (affineSourceKernel R X Y F hF f)).hom ≫
        sourceChangeKernelMap R X₂ X₃ Y h
            (affineSourceKernelSourceChangeIso R X Y F hF f g).hom ≫
          (affineSourceKernelSourceChangeIso R X Y F hF (g ≫ f) h).hom := by
  refine kernel_hom_ext R X₃ Y ?_
  refine (Iso.cancel_iso_hom_left
    (quasicoherentIntegralTransformSourceChangeIso R X₁ X₃ Y (h ≫ g)
      (affineSourceKernel R X Y F hF f)) _ _).mp ?_
  simp only [Functor.map_comp,
    sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso_assoc]
  simp only [Category.assoc, map_sourceChangeKernelMap,
    quasicoherentIntegralTransformSourceChangeIso_comp' R Y g h
      (affineSourceKernel R X Y F hF f),
    sourceChangeIso_hom_comp_map_affineSourceKernelSourceChangeIso,
    whiskerLeft_affineSourceKernelTriangle_assoc,
    Iso.inv_hom_id_map_assoc, Iso.hom_inv_id_assoc]
  refine Eq.trans (congrArg (fun z =>
    Functor.whiskerLeft (quasicoherentPushforward (Over.Hom.left (h ≫ g)))
          (affineSourceKernelIso R X Y F hF f).inv ≫
        Functor.whiskerRight (quasicoherentPushforwardComp (Over.Hom.left (h ≫ g))
          (Over.Hom.left f)).hom F ≫ z)
    (affineSourceKernelIso_hom_comp_map_eqToHom R X Y F hF f g h)) ?_
  exact pushforwardComp_coherence_assoc R X Y F hF f g h _

end Reassociation

end AlgebraicGeometry

end
