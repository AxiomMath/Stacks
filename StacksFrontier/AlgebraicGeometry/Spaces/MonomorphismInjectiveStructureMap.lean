module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpMono
public import StacksFrontier.Exercises.NonExercises.FaithfullyFlatSelfBaseChange
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Quasi-compact monomorphisms with injective structure map

**Stacks 0B8B.** A quasi-compact monomorphism `f : X ⟶ Y` of algebraic spaces over `S` is an
isomorphism as soon as, for every `T ⟶ Y`, the structure homomorphism
`𝒪_T ⟶ f_{T,*}𝒪_{X ×_Y T}` of the base change is injective.

The argument is the one of the source. The assertion reduces to surjectivity of `f` on
sections over an affine object `V` of the site: there the base change `Z = X ×_Y V` is
quasi-compact, hence has an affine étale surjective chart `U`, and the hypothesis applied to
every base change makes the global sections `Γ(V) ⟶ Γ(U)` universally injective. Both
self-base-change projections of `U ⟶ V` are étale because `Z ⟶ V` is a monomorphism, so
`Γ(V) ⟶ Γ(U)` is faithfully flat (Stacks 0GRM) and `U ⟶ V` is a flat surjective morphism of
affine schemes, that is a one-member fpqc covering. Along it the base change of `Z ⟶ V` is
split, and being also a monomorphism it is an isomorphism, so fpqc descent of isomorphisms
makes `Z ⟶ V` an isomorphism and produces the missing section.

## Main results

* `AlgebraicGeometry.Space.isIso_of_mono_of_forall_baseChange_mono_fSharp`: **Stacks 0B8B**.

The last step is fpqc descent of isomorphisms, **Stacks 041Y**, taken from
`AlgebraicGeometry.Space.isomorphisms_isLocalAtTarget_fpqc`.

## Implementation notes

Injectivity of a map of sheaves of commutative rings is monicity of it, and the map attached
to a base change is the structure homomorphism `fSharp` of the morphism of small étale ringed
topoi of Stacks 03G8. That this map is monic exactly when it is injective on sections over
every étale scheme chart, and that for a representable morphism those sections are pullback
of regular functions along the cartesian projection of schemes, are the two bridges
`AlgebraicGeometry.Space.mono_fSharp_iff_injective_structureMapApp` and
`AlgebraicGeometry.Space.injective_structureMapApp_iff`, both built from the chart API
of Stacks 03G8. They are public and live with the API they belong to: the first in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposHom.lean` beside `fSharp`, the
second in `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureMap.lean` beside the
chart projections, and this file imports both.

Fibre products of algebraic spaces are the chosen presheaf ones of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`. A scheme of the site is read as an algebraic
space by `AlgebraicGeometry.Space.repSpace`, which is `AlgebraicGeometry.schemeSpace`
written out as a pair — `AlgebraicGeometry.Space.repSpace_eq` identifies the two by `rfl` — so
that its underlying presheaf is syntactically the presheaf the scheme represents; the
definition of `schemeSpace` is semireducible and the étale and pullback instances needed here
are not found across it.

## References

* [Stacks Project, Tag 0B8B](https://stacks.math.columbia.edu/tag/0B8B)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 0GRM](https://stacks.math.columbia.edu/tag/0GRM)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-- The re-spelling agrees with `AlgebraicGeometry.schemeSpace`. -/
private theorem repSpace_eq (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) : schemeSpace U = schemeSpace U := rfl






/-- A ring map is universally injective as soon as it stays injective after tensoring with
every finitely presented module. -/
private theorem ringMapUniversallyInjective_of_finitePresentation
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q]
      [Module.FinitePresentation R Q],
      Function.Injective ((Algebra.linearMap R A).rTensor Q)) :
    Algebra.UniversallyInjective R A := by
  let f := Algebra.linearMap R A
  have hi : Function.Injective f := by
    intro x y he
    have hh : f.rTensor R (x ⊗ₜ[R] (1 : R)) = f.rTensor R (y ⊗ₜ[R] (1 : R)) := by
      simpa only [LinearMap.rTensor_tmul] using congrArg (fun a : A => a ⊗ₜ[R] (1 : R)) he
    simpa using congrArg (TensorProduct.rid R R) (h R hh)
  have he := LinearMap.exact_map_mkQ_range f
  apply (he.universallyExact_tfae hi (Submodule.mkQ_surjective _)).out 2 1 |>.mp
  intro Q _ _ _
  exact ⟨h Q, rTensor_exact Q he (Submodule.mkQ_surjective _),
    LinearMap.rTensor_surjective _ (Submodule.mkQ_surjective _)⟩

/-- Injectivity after tensoring with a module follows from injectivity of the right
coprojection of its trivial square-zero extension into the base change. -/
private theorem rTensor_injective_of_trivSqZeroExt
    (R A Q : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup Q] [Module R Q] [Module Rᵐᵒᵖ Q] [IsCentralScalar R Q]
    (h : Function.Injective
      (Algebra.TensorProduct.includeRight : TrivSqZeroExt R Q →ₐ[R]
        A ⊗[R] TrivSqZeroExt R Q)) :
    Function.Injective ((Algebra.linearMap R A).rTensor Q) := by
  intro x y hxy
  apply (TensorProduct.lid R Q).injective
  apply TrivSqZeroExt.inr_injective (R := R)
  apply h
  have hx (z : R ⊗[R] Q) :
      ((Algebra.linearMap R A).rTensor Q) z =
        (1 : A) ⊗ₜ[R] ((TensorProduct.lid R Q) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r q =>
      show (algebraMap R A r) ⊗ₜ[R] q = (1 : A) ⊗ₜ[R] (r • q)
      rw [TensorProduct.tmul_smul]
      congr 1
      exact Algebra.algebraMap_eq_smul_one r
    | add z w hz hw => simp [hz, hw, TensorProduct.tmul_add]
  simpa only [hx, LinearMap.lTensor_tmul, Algebra.TensorProduct.includeRight_apply,
    TrivSqZeroExt.inrHom_apply] using
    congrArg (LinearMap.lTensor A (TrivSqZeroExt.inrHom R Q)) hxy

/-- The trivial square-zero extension of a finite module is a finite algebra. -/
private theorem finite_trivSqZeroExt
    (R Q : Type u) [CommRing R] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] : Module.Finite R (TrivSqZeroExt R Q) :=
  inferInstanceAs (Module.Finite R (R × Q))

/-- A ring map is universally injective as soon as every algebra of finite type injects into
its base change along the map. -/
private theorem ringMapUniversallyInjective_of_finiteType_baseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (C : Type u) [CommRing C] [Algebra R C] [Algebra.FiniteType R C],
      Function.Injective (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C)) :
    Algebra.UniversallyInjective R A := by
  apply ringMapUniversallyInjective_of_finitePresentation
  intro Q _ _ _
  let : Module Rᵐᵒᵖ Q :=
    Module.compHom Q (RingEquiv.toOpposite R).symm.toRingHom
  let : IsCentralScalar R Q := ⟨fun _ _ => rfl⟩
  let : Module.Finite R (TrivSqZeroExt R Q) := finite_trivSqZeroExt R Q
  exact rTensor_injective_of_trivSqZeroExt R A Q (h (TrivSqZeroExt R Q))


attribute [local instance] schemeCutoff_hasPullbacks

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

/-- An isomorphism of presheaves on the big fppf site over `S` is representable and satisfies
every isomorphism-stable property of morphisms of schemes. -/
private theorem presheaf_inverseImage_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] [P.IsMultiplicative]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [IsIso f] :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda f, ?_⟩
  intro A C g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact P.of_isIso _

/-- A cartesian square stays cartesian when both legs of its cospan are composed with a
monomorphism. -/
private theorem isPullback_postcomp_mono
    {C : Type*} [Category* C] {P U V X Y : C}
    {p : P ⟶ U} {q : P ⟶ V} {a : U ⟶ X} {b : V ⟶ X}
    (f : X ⟶ Y) [Mono f] (h : IsPullback p q a b) :
    IsPullback p q (a ≫ f) (b ≫ f) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono a b f h.cone h.isLimit)

/-- Both projections of the self fibre product of a morphism of schemes are étale when that
morphism factors a monomorphism of presheaves through an étale chart of its source. -/
private theorem etale_selfBaseChange_of_etale_factorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} (f : F ⟶ yoneda.obj V) [Mono f]
    (a : yoneda.obj U ⟶ F) (g : U ⟶ V) (h : a ≫ f = yoneda.map g)
    (ha : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Etale (pullback.fst ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map g)) ∧
    Etale (pullback.snd ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map g)) := by
  let G := BigFppfOver.toScheme B S hS
  let p := ha.rep.fst' a
  let q := ha.rep.snd a
  have hpq : IsPullback (yoneda.map p) (yoneda.map q) a a := ha.rep.isPullback' a
  have hcomp := isPullback_postcomp_mono f hpq
  rw [h] at hcomp
  have hsite : IsPullback p q g g := IsPullback.of_map yoneda
    (yoneda.map_injective (by simpa only [Functor.map_comp] using hcomp.w)) hcomp
  have hsch := hsite.map G
  have hp : Etale (G.map p) := ha.property a (yoneda.map q) p hpq.flip
  have hq : Etale (G.map q) := ha.property_snd a
  constructor
  · rw [← hsch.isoPullback_inv_fst]
    infer_instance
  · rw [← hsch.isoPullback_inv_snd]
    infer_instance

/-- A monomorphism of algebraic spaces through which an fpqc covering of its target factors
is an isomorphism. -/
private theorem isIso_of_mono_of_fpqc_factorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f]
    {I : Type u} (U : I → AlgebraicSpaces B S hS)
    (a : ∀ i, U i ⟶ X)
    (hcover : Space.IsFpqcCovering B S hS (fun i => (a i ≫ f).hom)) :
    IsIso f := by
  let K := Space.Topology.precoverage.{u, u} .fpqc B S hS
  let : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget K :=
    isomorphisms_isLocalAtTarget_fpqc.{u, u} B S hS
  have hmem : Presieve.ofArrows U (fun i => a i ≫ f) ∈ K Y :=
    ⟨I, U, (fun i => a i ≫ f), rfl, Y.property, (fun i => (U i).property), hcover⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := MorphismProperty.isomorphisms _) hmem
  rintro V g _ ⟨i⟩
  have : IsSplitEpi (pullback.snd f (a i ≫ f)) :=
    ⟨⟨pullback.lift (a i) (𝟙 (U i)) (by simp), pullback.lift_snd _ _ _⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- A universally injective ring map whose two self-base-change projections of spectra are
flat has flat and surjective spectrum map. -/
private theorem flat_and_surjective_specMap_of_flat_selfBaseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hleft : Flat (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (hright : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (hinj : Algebra.UniversallyInjective R A) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  apply Algebra.faithfullyFlat_of_flat_selfTensor_of_universallyInjective
    (hBC := hinj)
  · apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom)).mp
    have h := Flat.comp (pullbackSpecIso R A A).inv
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    convert h using 1
    exact (pullbackSpecIso_inv_fst R A A).symm
  · apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom)).mp
    have h := Flat.comp (pullbackSpecIso R A A).inv
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    convert h using 1
    exact (pullbackSpecIso_inv_snd R A A).symm

/-- A morphism of affine schemes whose two self-base-change projections are flat and whose
map of global sections is universally injective is flat and surjective. -/
private theorem flat_and_surjective_of_affine_selfBaseChange
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (b : U ⟶ V)
    [Flat (pullback.fst b b)] [Flat (pullback.snd b b)]
    (hinj : letI := b.appTop.hom.toAlgebra
      Algebra.UniversallyInjective Γ(V, ⊤) Γ(U, ⊤)) :
    Flat b ∧ Surjective b := by
  let := b.appTop.hom.toAlgebra
  let s := Spec.map b.appTop
  let l := pullback.fst b b ≫ U.isoSpec.hom
  let r := pullback.snd b b ≫ U.isoSpec.hom
  have sq : IsPullback l r s s := by
    apply (IsPullback.of_hasPullback b b).of_iso
      (Iso.refl _) U.isoSpec U.isoSpec V.isoSpec
    · simp [l]
    · simp [r]
    · exact (ΓSpec.adjunction.unit_naturality b).symm
    · exact (ΓSpec.adjunction.unit_naturality b).symm
  have hl : Flat (pullback.fst s s) := by
    rw [← sq.isoPullback_inv_fst]
    dsimp [l]
    infer_instance
  have hr : Flat (pullback.snd s s) := by
    rw [← sq.isoPullback_inv_snd]
    dsimp [r]
    infer_instance
  obtain ⟨hf, hs⟩ := flat_and_surjective_specMap_of_flat_selfBaseChange
    Γ(V, ⊤) Γ(U, ⊤) hl hr hinj
  have : Flat s := hf
  have : Surjective s := hs
  have hn : U.isoSpec.hom ≫ s = b ≫ V.isoSpec.hom :=
    ΓSpec.adjunction.unit_naturality b
  have hb : b = U.isoSpec.hom ≫ s ≫ V.isoSpec.inv := by
    rw [← Category.assoc, hn]
    simp
  rw [hb]
  constructor <;> infer_instance

/-- A ring map whose spectrum map has monic global sections is injective. -/
private theorem injective_of_mono_globalSections_specMap
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    [hmono : Mono (Scheme.Γ.map (Spec.map f).op)] : Function.Injective f := by
  have h : Mono ((Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (Spec.map f).op) :=
    @mono_comp _ _ _ _ _ _ inferInstance _ hmono
  have hnat : f ≫ (Scheme.ΓSpecIso A).inv =
      (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (Spec.map f).op := by
    rw [Scheme.Γ_map_op]
    exact Scheme.ΓSpecIso_inv_naturality f
  have h2 : Mono (f ≫ (Scheme.ΓSpecIso A).inv) := by
    rw [hnat]
    exact h
  have : Mono f := mono_of_mono f (Scheme.ΓSpecIso A).inv
  exact (CategoryTheory.mono_iff_injective ((forget CommRingCat).map f)).mp inferInstance

/-- A ring map is universally injective when, for every algebra of finite type, the global
sections of the base change of its spectrum map are monic. -/
private theorem universallyInjective_of_mono_globalSections_baseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (C : Type u) [CommRing C] [Algebra R C] [Algebra.FiniteType R C],
      Mono (Scheme.Γ.map (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C)))).op)) :
    Algebra.UniversallyInjective R A := by
  apply ringMapUniversallyInjective_of_finiteType_baseChange
  intro C _ _ _
  let j : C →ₐ[R] A ⊗[R] C := Algebra.TensorProduct.includeRight
  have hp := h C
  have hΓ : Mono (Scheme.Γ.map ((pullbackSpecIso R A C).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C)))).op) := by
    rw [op_comp, Functor.map_comp]
    infer_instance
  have hj : Mono (Scheme.Γ.map (Spec.map (CommRingCat.ofHom j.toRingHom)).op) :=
    (congrArg
      (fun p : Spec (CommRingCat.of (A ⊗[R] C)) ⟶ Spec (CommRingCat.of C) =>
        Mono (Scheme.Γ.map p.op)) (pullbackSpecIso_inv_snd R A C)) ▸ hΓ
  exact injective_of_mono_globalSections_specMap (CommRingCat.ofHom j.toRingHom)

/-- A morphism of affine objects of the site has universally injective map of global sections
when every base change of it has monic global sections. -/
private theorem universallyInjective_appTop_of_mono_globalSections_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (b : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (h : ∀ (T : BigFppfOver B S hS) (g : T ⟶ V),
      Mono (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map (pullback.fst g b)).op)) :
    let G := BigFppfOver.toScheme B S hS
    letI := (G.map b).appTop.hom.toAlgebra
    Algebra.UniversallyInjective Γ(G.obj V, ⊤) Γ(G.obj U, ⊤) := by
  let G := BigFppfOver.toScheme B S hS
  let R := Γ(G.obj V, ⊤)
  let A := Γ(G.obj U, ⊤)
  let := (G.map b).appTop.hom.toAlgebra
  have := hU
  have := hV
  apply universallyInjective_of_mono_globalSections_baseChange R A
  intro C _ _ _
  have hR : (Spec (CommRingCat.of R)).size < B.cutoff :=
    (Scheme.size_congr (G.obj V).isoSpec) ▸ V.left.property
  have hC : B.Contains (Spec (CommRingCat.of C)) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R C hR
  let k : Spec (CommRingCat.of C) ⟶ G.obj V :=
    Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ (G.obj V).isoSpec.inv
  let W : BigFppfOver B S hS :=
    Over.mk ((ObjectProperty.homMk k : B.obj hC ⟶ V.left) ≫ V.hom)
  let w : W ⟶ V := Over.homMk (ObjectProperty.homMk k) rfl
  have hw := h W w
  let a := G.map (pullback.fst w b)
  let c := G.map (pullback.snd w b) ≫ (G.obj U).isoSpec.hom
  have sq : IsPullback a c
      (Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    apply ((IsPullback.of_hasPullback w b).map G).of_iso
      (Iso.refl _) (Iso.refl _) (G.obj U).isoSpec (G.obj V).isoSpec
    · simp [a]
    · simp [c]
    · show k ≫ (G.obj V).isoSpec.hom = _
      simp [k]
    · exact (ΓSpec.adjunction.unit_naturality (G.map b)).symm
  have hm : Mono (Scheme.Γ.map (sq.flip.isoPullback.inv ≫ a).op) := by
    rw [op_comp, Functor.map_comp]
    infer_instance
  exact (congrArg
    (fun p => Mono (Scheme.Γ.map p.op)) sq.flip.isoPullback_inv_snd) ▸ hm

/-- The global sections of a flat surjective morphism of schemes are monic. -/
private theorem mono_globalSections_of_flat_surjective
    {U V : Scheme.{u}} (p : U ⟶ V) [Flat p] [Surjective p] :
    Mono (Scheme.Γ.map p.op) := by
  have : Epi p := Flat.epi_of_flat_of_surjective p
  infer_instance

/-- The structure homomorphism of a representable étale surjective morphism of algebraic
spaces is a monomorphism. -/
private theorem mono_fSharp_of_etale_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (he : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (hs : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    Mono (smallEtaleRingedToposHom B S hS f).fSharp := by
  rw [mono_fSharp_iff_injective_structureMapApp B S hS f]
  intro V
  rw [injective_structureMapApp_iff B S hS f he.rep V]
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map (he.rep.snd V.1.hom)) :=
    he.property_snd V.1.hom
  have hSur : Surjective ((BigFppfOver.toScheme B S hS).map (he.rep.snd V.1.hom)) :=
    hs.property V.1.hom (he.rep.fst V.1.hom) (he.rep.snd V.1.hom) (he.rep.isPullback V.1.hom)
  have : Mono (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (he.rep.snd V.1.hom)).op) :=
    mono_globalSections_of_flat_surjective _
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp this

/-- A morphism of the site whose morphism of algebraic spaces has monic structure
homomorphism has monic global sections. -/
private theorem mono_globalSections_of_mono_fSharp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (h : Mono (smallEtaleRingedToposHom B S hS
      (ObjectProperty.homMk (yoneda.map g) :
        schemeSpace U ⟶ schemeSpace V)).fSharp) :
    Mono (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op) := by
  let f : schemeSpace U ⟶ schemeSpace V := ObjectProperty.homMk (yoneda.map g)
  have hf : yoneda.relativelyRepresentable f.hom := Functor.relativelyRepresentable.map yoneda g
  let V₀ : SmallEtale B S hS (schemeSpace V).obj :=
    ⟨CostructuredArrow.mk (𝟙 _), presheaf_inverseImage_of_isIso B S hS (𝟙 (yoneda.obj V))⟩
  have hinj := (mono_fSharp_iff_injective_structureMapApp B S hS f).mp h V₀
  rw [injective_structureMapApp_iff B S hS f hf V₀] at hinj
  let W := (smallBaseChange B S hS f hf).obj V₀
  let u : W.1.left ⟶ U := yoneda.preimage W.1.hom
  have hpre : yoneda.map u = W.1.hom := yoneda.map_preimage _
  have hcomm := chartBaseChangeMap_comm B S hS f W V₀
    (smallBaseChangeComparisonIso B S hS f hf V₀).hom
  rw [chartBaseChangeMap_chartBaseChangeArrow B S hS f hf V₀] at hcomm
  have hu : u ≫ g = hf.snd V₀.1.hom := by
    apply yoneda.map_injective
    refine (yoneda.map_comp u g).trans ?_
    refine Eq.trans ?_ (Category.comp_id (yoneda.map (hf.snd V₀.1.hom)))
    refine Eq.trans ?_ hcomm
    exact congrArg (fun t => t ≫ yoneda.map g) hpre
  have hmono : Mono (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (u ≫ g)).op) := by
    have h0 : ∀ k : W.1.left ⟶ V, k = hf.snd V₀.1.hom →
        Mono (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op) := by
      rintro k rfl
      exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr hinj
    exact h0 (u ≫ g) hu
  rw [Functor.map_comp, op_comp, Functor.map_comp] at hmono
  exact mono_of_mono _ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map u).op)

/-- Two morphisms of algebraic spaces with monic structure homomorphism have composite with
monic structure homomorphism. -/
private theorem mono_fSharp_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono (Space.smallEtaleRingedToposHom B S hS f).fSharp]
    [Mono (Space.smallEtaleRingedToposHom B S hS g).fSharp] :
    Mono (Space.smallEtaleRingedToposHom B S hS (f ≫ g)).fSharp := by
  rw [← Space.smallEtaleRingedToposHom_comp_fSharp B S hS f g]
  let := (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
    (Space.smallEtaleRingedToposHom B S hS g).toToposHom).isRightAdjoint
  have hmid : Mono ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (Space.smallEtaleRingedToposHom B S hS g).toToposHom).map
      (Space.smallEtaleRingedToposHom B S hS f).fSharp) :=
    preserves_mono_of_preservesLimit _ _
  have hlast : Mono ((Space.smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
      (Space.smallEtaleRingedTopos B S hS X).O) :=
    inferInstanceAs (Mono ((Space.smallEtaleRingedToposHom_compRingIso B S hS f g).app
      (Space.smallEtaleRingedTopos B S hS X).O).hom)
  dsimp only [RingedToposHom.comp]
  exact @mono_comp _ _ _ _ _ _ inferInstance _ hlast

/-- The structure homomorphism of an isomorphism of algebraic spaces is a monomorphism. -/
private theorem mono_fSharp_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [IsIso f] :
    Mono (Space.smallEtaleRingedToposHom B S hS f).fSharp := by
  have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
  exact mono_fSharp_of_etale_surjective B S hS f
    (presheaf_inverseImage_of_isIso B S hS _) (presheaf_inverseImage_of_isIso B S hS _)

/-- Monicity of the structure homomorphism of the chosen base changes of a morphism gives it
for the first projection of any cartesian square over that morphism. -/
private theorem mono_fSharp_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hinj : ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      Mono (Space.smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
          AlgebraicSpaces.fiberProduct B S hS g f ⟶ T)).fSharp)
    {P T : AlgebraicSpaces B S hS}
    {p : P ⟶ T} {q : P ⟶ X} {g : T ⟶ Y} (sq : IsPullback p q g f) :
    Mono (Space.smallEtaleRingedToposHom B S hS p).fSharp := by
  let t := AlgebraicSpaces.isPullback_fiberProduct B S hS g f
  let e := IsPullback.isoIsPullback T X sq t
  have : Mono (Space.smallEtaleRingedToposHom B S hS e.hom).fSharp :=
    mono_fSharp_of_isIso B S hS e.hom
  have := hinj T g
  rw [← IsPullback.isoIsPullback_hom_fst T X sq t]
  exact mono_fSharp_comp B S hS e.hom _

/-- Monicity of the structure homomorphisms of the chosen base changes of a morphism passes to
the chosen base changes of one of those base changes. -/
private theorem forall_baseChange_mono_fSharp_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hinj : ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      Mono (Space.smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
          AlgebraicSpaces.fiberProduct B S hS g f ⟶ T)).fSharp)
    (T : AlgebraicSpaces B S hS) (g : T ⟶ Y)
    (W : AlgebraicSpaces B S hS) (h : W ⟶ T) :
    let p : AlgebraicSpaces.fiberProduct B S hS g f ⟶ T :=
      ObjectProperty.homMk (pullback.fst g.hom f.hom)
    Mono (Space.smallEtaleRingedToposHom B S hS
      (ObjectProperty.homMk (pullback.fst h.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS h p ⟶ W)).fSharp := by
  let p : AlgebraicSpaces.fiberProduct B S hS g f ⟶ T :=
    ObjectProperty.homMk (pullback.fst g.hom f.hom)
  exact mono_fSharp_of_isPullback B S hS f hinj
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS h p).paste_vert
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g f))

/-- Every base change of a morphism of the site has monic global sections when that morphism
factors, through an étale surjective chart, a morphism of algebraic spaces all of whose base
changes have monic structure homomorphism. -/
private theorem mono_globalSections_baseChange_of_etale_surjective_factorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    {U V : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace V) (a : schemeSpace U ⟶ X)
    (g : U ⟶ V) (ha : a.hom ≫ f.hom = yoneda.map g)
    (he : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a.hom)
    (hs : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a.hom)
    (hinj : ∀ (T : AlgebraicSpaces B S hS)
      (h : T ⟶ schemeSpace V),
      Mono (Space.smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (pullback.fst h.hom f.hom) :
          AlgebraicSpaces.fiberProduct B S hS h f ⟶ T)).fSharp)
    (T : BigFppfOver B S hS) (h : T ⟶ V) :
    Mono (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (pullback.fst h g)).op) := by
  let hsp : schemeSpace T ⟶ schemeSpace V :=
    ObjectProperty.homMk (yoneda.map h)
  let Z := AlgebraicSpaces.fiberProduct B S hS hsp f
  let p : Z ⟶ schemeSpace T := ObjectProperty.homMk (pullback.fst hsp.hom f.hom)
  let q : Z ⟶ X := ObjectProperty.homMk (pullback.snd hsp.hom f.hom)
  let b : schemeSpace (pullback h g) ⟶ Z :=
    ObjectProperty.homMk (pullback.lift (yoneda.map (pullback.fst h g))
      (yoneda.map (pullback.snd h g) ≫ a.hom) (by
        have hcond : yoneda.map (pullback.fst h g) ≫ yoneda.map h =
            yoneda.map (pullback.snd h g) ≫ yoneda.map g := by
          rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
        exact hcond.trans
          ((congrArg (fun t => yoneda.map (pullback.snd h g) ≫ t) ha).symm.trans
            (Category.assoc _ _ _).symm)))
  have hout : IsPullback (b.hom ≫ p.hom) (yoneda.map (pullback.snd h g))
      hsp.hom (a.hom ≫ f.hom) := by
    have h0 : b.hom ≫ p.hom = yoneda.map (pullback.fst h g) := pullback.lift_fst _ _ _
    have hy := (IsPullback.of_hasPullback h g).map yoneda
    rwa [← h0, ← ha] at hy
  have hpb : IsPullback b.hom (yoneda.map (pullback.snd h g)) q.hom a.hom :=
    hout.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback hsp.hom f.hom)
  have hb : Mono (Space.smallEtaleRingedToposHom B S hS b).fSharp := by
    apply mono_fSharp_of_etale_surjective B S hS b
    · let := MorphismProperty.relative_isStableUnderBaseChange
        (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (F := yoneda)
      exact MorphismProperty.of_isPullback hpb.flip he
    · let := MorphismProperty.relative_isStableUnderBaseChange
        (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (F := yoneda)
      exact MorphismProperty.of_isPullback hpb.flip hs
  have hp := hinj (schemeSpace T) hsp
  have hc : b ≫ p = ObjectProperty.homMk (yoneda.map (pullback.fst h g)) := by
    apply ObjectProperty.hom_ext
    exact pullback.lift_fst _ _ _
  have hm := mono_fSharp_comp B S hS b p
  rw [hc] at hm
  exact mono_globalSections_of_mono_fSharp B S hS (pullback.fst h g) hm

/-- A flat surjective morphism of affine objects of the site is a one-member fpqc covering of
algebraic spaces. -/
private theorem isFpqcCovering_yoneda_map_of_flat_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (b : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hf : Flat ((BigFppfOver.toScheme B S hS).map b))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map b)) :
    Space.IsFpqcCovering B S hS (fun _ : PUnit.{u + 1} => yoneda.map b) := by
  let G := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  constructor
  · intro i
    apply (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
      (@Flat) Flat.isEtaleLocalOnSourceAndTarget
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (yoneda.map b)).mpr
    exact ⟨U, V, 𝟙 _, 𝟙 _, b, presheaf_inverseImage_of_isIso B S hS _,
      presheaf_inverseImage_of_isIso B S hS _, presheaf_inverseImage_of_isIso B S hS _,
      by simp, hf⟩
  · intro T g
    let h : A.obj T ⟶ V := yoneda.preimage g
    have hg : yoneda.map h = g := yoneda.map_preimage _
    have sq := (IsPullback.of_hasPullback h b).map G
    have : IsAffine (G.obj U) := hU
    have : IsAffine (G.obj V) := hV
    have : IsAffine (G.obj (A.obj T)) := T.property
    have hW : IsAffine (G.obj (pullback h b)) := IsAffine.of_isIso sq.isoPullback.hom
    let W : BigAffineFppf B S hS := ⟨pullback h b, hW⟩
    let q : W ⟶ T := ObjectProperty.homMk (pullback.fst h b)
    let E : PreZeroHypercover.{u + 1} T := .singleton q
    refine ⟨E, inferInstance, ?_, ?_⟩
    · have : Flat (G.map (pullback.fst h b)) :=
        MorphismProperty.of_isPullback sq.flip hf
      have : Surjective (G.map (pullback.fst h b)) :=
        MorphismProperty.of_isPullback sq.flip hs
      rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
      exact (G.map (pullback.fst h b)).singleton_mem_fpqcPrecoverage
    · intro j
      refine ⟨PUnit.unit, yoneda.map (pullback.snd h b), ?_⟩
      show yoneda.map (pullback.snd h b) ≫ yoneda.map b =
        yoneda.map (pullback.fst h b) ≫ g
      rw [← hg, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- A monomorphism of algebraic spaces is a monomorphism of the underlying presheaves. -/
private theorem mono_hom_of_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f] :
    Mono f.hom := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  let Z : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj U.unop, isAlgebraicSpace_yoneda B S hS U.unop⟩
  let a : Z ⟶ X := ObjectProperty.homMk (yonedaEquiv.symm x)
  let b : Z ⟶ X := ObjectProperty.homMk (yonedaEquiv.symm y)
  have hxa : yonedaEquiv a.hom = x := yonedaEquiv.apply_symm_apply x
  have hxb : yonedaEquiv b.hom = y := yonedaEquiv.apply_symm_apply y
  have hab : a ≫ f = b ≫ f := by
    apply ObjectProperty.hom_ext
    apply yonedaEquiv.injective
    show yonedaEquiv (a.hom ≫ f.hom) = yonedaEquiv (b.hom ≫ f.hom)
    rw [yonedaEquiv_comp, yonedaEquiv_comp, hxa, hxb]
    exact hxy
  rw [← hxa, ← hxb, (cancel_mono f).1 hab]

/-- A monomorphism of algebraic spaces which is surjective on sections over every affine object
of the site is an isomorphism. -/
private theorem isIso_of_mono_of_surjective_affine_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f]
    (h : ∀ T : BigAffineFppf B S hS,
      Function.Surjective (f.hom.app (.op
        ((BigAffineFppf.inclusion B S hS).obj T)))) : IsIso f := by
  have : Mono f.hom := mono_hom_of_mono B S hS f
  let J := BigFppfOver.topology B S hS
  let F : Sheaf J (Type u) := ⟨X.obj, X.property.isSheaf⟩
  let G : Sheaf J (Type u) := ⟨Y.obj, Y.property.isSheaf⟩
  let φ : F ⟶ G := ⟨f.hom⟩
  have hφ : IsIso φ := by
    let A := BigAffineFppf.inclusion B S hS
    let K := BigAffineFppf.topology B S hS
    let : A.IsCoverDense J := Functor.IsDenseSubsite.isCoverDense K J A
    apply Functor.IsCoverDense.iso_of_restrict_iso (G := A)
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    show Function.Bijective (f.hom.app (.op (A.obj T.unop)))
    exact ⟨(CategoryTheory.mono_iff_injective _).mp inferInstance, h T.unop⟩
  have : IsIso f.hom := (sheafToPresheaf J (Type u)).map_isIso φ
  exact (ObjectProperty.isIso_hom_iff f).mp this

/-- **Stacks 0B8B.** A quasi-compact monomorphism of algebraic spaces over `S` whose structure
homomorphism `𝒪_T ⟶ f_{T,*}𝒪_{X ×_Y T}` is a monomorphism for every `T ⟶ Y` is an
isomorphism. -/
@[stacks 0B8B]
public theorem isIso_of_mono_of_forall_baseChange_mono_fSharp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : Space.IsQuasiCompact B S hS f.hom) [Mono f]
    (hinj : ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      Mono (Space.smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
          AlgebraicSpaces.fiberProduct B S hS g f ⟶ T)).fSharp) :
    IsIso f := by
  have : Mono f.hom := mono_hom_of_mono B S hS f
  apply isIso_of_mono_of_surjective_affine_sections B S hS f
  intro T y
  let V := (BigAffineFppf.inclusion B S hS).obj T
  let g : schemeSpace V ⟶ Y := ObjectProperty.homMk (yonedaEquiv.symm y)
  let Z := AlgebraicSpaces.fiberProduct B S hS g f
  let p : Z ⟶ schemeSpace V := ObjectProperty.homMk (pullback.fst g.hom f.hom)
  have : Mono p.hom := inferInstanceAs (Mono (pullback.fst g.hom f.hom))
  have hVqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj V) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := T.property
    refine ⟨V, 𝟙 _, inferInstance, presheaf_inverseImage_of_isIso B S hS _, ?_⟩
    intro U a ha
    simpa using ha
  have hZqc := hqc _ (isAlgebraicSpace_yoneda B S hS V) hVqc g.hom
  obtain ⟨U, a, hU, hs, he⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS Z.obj Z.property).mp hZqc
  let b : U ⟶ V := yoneda.preimage (a ≫ p.hom)
  have hab : a ≫ p.hom = yoneda.map b := (yoneda.map_preimage _).symm
  have haEt : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
    simpa using he U (𝟙 _) (presheaf_inverseImage_of_isIso B S hS _)
  have hbself := @etale_selfBaseChange_of_etale_factorization B S hS _ _ _ p.hom
    (‹Mono p.hom›) a b hab haEt
  have hbΓ := mono_globalSections_baseChange_of_etale_surjective_factorization
    B S hS p (ObjectProperty.homMk a) b hab haEt hs
      (forall_baseChange_mono_fSharp_pullback B S hS f hinj _ g)
  have hbui := universallyInjective_appTop_of_mono_globalSections_baseChange
    B S hS b hU T.property hbΓ
  let G := BigFppfOver.toScheme B S hS
  have : IsAffine (G.obj U) := hU
  have : IsAffine (G.obj V) := T.property
  have : Etale (pullback.fst (G.map b) (G.map b)) := hbself.1
  have : Etale (pullback.snd (G.map b) (G.map b)) := hbself.2
  obtain ⟨hbflat, hbsurj⟩ := flat_and_surjective_of_affine_selfBaseChange (G.map b) hbui
  have hcover := isFpqcCovering_yoneda_map_of_flat_surjective
    B S hS b hU T.property hbflat hbsurj
  have : Mono p :=
    (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono p.hom))
  have : IsIso p := isIso_of_mono_of_fpqc_factorization B S hS p
    (fun _ : PUnit.{u + 1} => schemeSpace U)
    (fun _ => ObjectProperty.homMk a) (by
      show Space.IsFpqcCovering B S hS (fun _ : PUnit.{u + 1} => a ≫ p.hom)
      rwa [hab])
  let q : Z ⟶ X := ObjectProperty.homMk (pullback.snd g.hom f.hom)
  refine ⟨yonedaEquiv ((inv p ≫ q).hom), ?_⟩
  have hpq : q ≫ f = p ≫ g := by
    apply ObjectProperty.hom_ext
    exact (pullback.condition (f := g.hom) (g := f.hom)).symm
  have hlift : inv p ≫ q ≫ f = g := by
    rw [hpq]
    simp
  refine (yonedaEquiv_comp (inv p ≫ q).hom f.hom).symm.trans ?_
  show yonedaEquiv (((inv p ≫ q) ≫ f).hom) = y
  rw [Category.assoc, hlift]
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Space

end
