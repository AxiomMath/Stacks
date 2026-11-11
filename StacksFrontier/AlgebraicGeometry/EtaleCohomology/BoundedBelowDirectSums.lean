module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusCoproducts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact

/-!
# Derived direct image and direct sums bounded below

[Stacks, Tag 0GIW] says that for a quasi-compact and quasi-separated morphism of schemes
`f : X ⟶ Y` and a family `K_i`, `i ∈ I`, of objects of `D(X_étale)` admitting a common lower
bound `a` — that is, `H^n(K_i) = 0` for `n < a` and all `i ∈ I` — one has
`Rf_*(⨁_i K_i) = ⨁_i Rf_* K_i`.

The argument of the source is: resolve each `K_i` by a complex of injective sheaves lying in
degrees `≥ a`, which is the bounded below half of [Stacks, Tag 07D9]; the termwise direct sum of
those resolutions again lies in degrees `≥ a`, and its terms are `f_*`-acyclic because each
`R^q f_*` commutes with the direct sum, [Stacks, Tag 09Z1]; so Leray's acyclicity lemma,
[Stacks, Tag 015E], computes `Rf_*` termwise on each resolution and on their direct sum, and the
comparison of the two cofans is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.preservesColimit_rightDerivedFunctorPlus_of_isGE` — the statement for
  an arbitrary left exact functor between Grothendieck abelian categories, with the vanishing
  input as a hypothesis.
* `Stacks.EtaleCohomology.preservesColimit_etaleModuleDerivedDirectImage_of_isGE` — the same
  for the bounded below derived direct image of sheaves of `Λ`-modules on small étale sites,
  given that every `R^q f_*` commutes with the direct sum.

The tag itself, for abelian sheaves and the unbounded `Rf_*`, is
`Stacks.EtaleCohomology.preservesColimit_etaleAbelianDerivedDirectImage_of_isGE`; the
`Λ`-module statement with no hypothesis beyond the source's is
`Stacks.EtaleCohomology.preservesColimit_etaleModuleDerivedDirectImage_of_isGE_univ`.

## Implementation notes

*The input on higher direct images.* That the ordinary higher direct images `R^q f_*` on the
small étale site commute with direct sums is [Stacks, Tag 09Z1]. It is an argument `hsums` of the
statements here, which sit below its proof in the import order: for sheaves of `Λ`-modules along
a quasi-compact and quasi-separated morphism it is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`,
and `preservesColimit_etaleModuleDerivedDirectImage_of_isGE_univ` feeds it in.

*Bounded below.* The source states the lemma in `D(X_étale)`, but its hypothesis
`H^n(K_i) = 0` for `n < a` places every `K_i`, and hence their direct sum, in `D⁺(X_étale)`. The
statement here is therefore read on `D⁺` and for the bounded below derived direct image
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImage`, which is the shape its consumer needs:
the hypothesis
`hProper` of
`Stacks.EtaleCohomology.DerivedUpperShriek.preservesColimit_derivedLowerShriek_of_isGE`, which
is [Stacks, Tag 0G29] (1) and cites this tag for it.

*Coefficients.* The source's `D(X_étale)` is the derived category of abelian sheaves, the case
`Λ = ℤ`; the statement below is for an arbitrary ring `Λ`.

*Direct sums.* "Commutes with direct sums" is
`CategoryTheory.Limits.PreservesColimit` for a discrete diagram: the image of a coproduct cocone
is a coproduct cocone, which is the source's `Rf_*(⨁ K_i) = ⨁ Rf_* K_i` read through the
canonical comparison, and presupposes no existence of either coproduct.

*The index universe.* `I` ranges over `Type (max (u + 1) r)`, the universe controlling the
Grothendieck axioms of the two categories of sheaves of `Λ`-modules. This is forced rather than
an artefact: the termwise direct sum of the injective resolutions is formed inside those
categories, so the index universe and the Grothendieck universe are the same one.

## References

* [Stacks Project, Tag 0GIW](https://stacks.math.columbia.edu/tag/0GIW)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w v u v' u' r

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus

namespace Stacks.EtaleCohomology

section Machinery

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [EnoughInjectives A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] {I : Type w}

/-- A colimit cocone stays one after a comparison that is invertible at every object of the
diagram and at the apex. -/
def isColimitMapCoconeOfIsIso {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
    {J : Type*} [Category J] (K : J ⥤ C₁) (c : Cocone K) (G H : C₁ ⥤ C₂) (α : G ⟶ H)
    (hlegs : ∀ j : J, IsIso (α.app (K.obj j))) (hapex : IsIso (α.app c.pt))
    (hG : IsColimit (G.mapCocone c)) : IsColimit (H.mapCocone c) := by
  let (j : J) : IsIso (α.app (K.obj j)) := hlegs j
  have : IsIso (Functor.whiskerLeft K α) :=
    (NatTrans.isIso_iff_isIso_app _).2 (fun j ↦ hlegs j)
  let e : K ⋙ G ≅ K ⋙ H := asIso (Functor.whiskerLeft K α)
  have h : IsColimit ((Cocone.precompose e.inv).obj (G.mapCocone c)) :=
    (IsColimit.precomposeHomEquiv e.symm (G.mapCocone c)).symm hG
  let : IsIso (α.app c.pt) := hapex
  refine IsColimit.ofIsoColimit h (Cocone.ext (asIso (α.app c.pt)) ?_)
  intro j
  simp only [Cocone.precompose_obj_ι, e, Functor.mapCocone_ι_app]
  simp

/-- **A coproduct cofan of complexes with a common strict lower bound whose apex has the same
bound is carried by the localization functor to a coproduct cofan in `D⁺`.** This is
`DerivedCategory.Plus.isColimitTermwiseDirectSumCofan` for an arbitrary coproduct cofan rather
than the canonical termwise direct sum, obtained by transport along the comparison of the two
apexes. -/
def isColimitCofanOfIsGE {N : I → CochainComplex B ℤ} (a : ℤ)
    [∀ i, (N i).IsStrictlyGE a] (X : CochainComplex B ℤ) [X.IsStrictlyGE a]
    (f : ∀ i, N i ⟶ X) (h : IsColimit (Cofan.mk X f)) :
    IsColimit (Cofan.mk (DerivedCategory.Plus.ofIsGE X a)
      (fun i ↦ (ObjectProperty.homMk (DerivedCategory.Q.map (f i)) :
        DerivedCategory.Plus.ofIsGE (N i) a ⟶ DerivedCategory.Plus.ofIsGE X a))) := by
  have hprod := coproductIsCoproduct N
  let e : (∐ N) ≅ X := hprod.coconePointUniqueUpToIso h
  have he (i : I) : Limits.Sigma.ι N i ≫ e.hom = f i :=
    hprod.comp_coconePointUniqueUpToIso_hom h ⟨i⟩
  have : (∐ N).IsStrictlyGE a := CochainComplex.isStrictlyGE_coproduct N a
  let E : DerivedCategory.Plus.ofIsGE (∐ N) a ≅ DerivedCategory.Plus.ofIsGE X a :=
    { hom := ObjectProperty.homMk (DerivedCategory.Q.map e.hom)
      inv := ObjectProperty.homMk (DerivedCategory.Q.map e.inv)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        change DerivedCategory.Q.map e.hom ≫ DerivedCategory.Q.map e.inv = 𝟙 _
        rw [← Functor.map_comp, e.hom_inv_id]
        exact DerivedCategory.Q.map_id _
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        change DerivedCategory.Q.map e.inv ≫ DerivedCategory.Q.map e.hom = 𝟙 _
        rw [← Functor.map_comp, e.inv_hom_id]
        exact DerivedCategory.Q.map_id _ }
  refine IsColimit.ofIsoColimit (DerivedCategory.Plus.isColimitTermwiseDirectSumCofan N a)
    (Cocone.ext E ?_)
  intro j
  apply ObjectProperty.hom_ext
  change DerivedCategory.Q.map (Limits.Sigma.ι N j.as) ≫ DerivedCategory.Q.map e.hom =
    DerivedCategory.Q.map (f j.as)
  rw [← DerivedCategory.Q.map_comp, he]

omit [IsGrothendieckAbelian.{w} A] [IsGrothendieckAbelian.{w} B] [PreservesFiniteLimits F] in
/-- **The comparison `Q(F K) ⟶ RF(Q K)` is invertible on a bounded below complex all of whose
terms are right acyclic.** This is [Stacks, Tag 015E], Leray's acyclicity lemma, read on the
derived-functor unit of bounded below cochain complexes. -/
lemma isIso_mapCochainComplexPlusDerivedUnit_app (K : CochainComplex.Plus A)
    (hK : ∀ n, F.rightAcyclic (K.obj.X n)) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit F).app K) := by
  have hu : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj K)) := by
    have hβ := F.isIso_totalRightDerivedUnit_app_of_rightAcyclic K.obj K.property hK
    have hd := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso A) _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))).1 inferInstance
    rw [← Functor.rightDerived_fac_app F.rightDerivedFunctorPlus
      F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A)] at hβ
    rwa [isIso_comp_right_iff] at hβ
  have h1 : IsIso ((DerivedCategory.Plus.quotientCompQhIso B).inv.app
      (F.mapCochainComplexPlus.obj K)) := inferInstance
  have h3 : IsIso (F.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso A).hom.app K)) := inferInstance
  rw [Functor.mapCochainComplexPlusDerivedUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ hu h3)

/-- **The bounded below right derived functor commutes with a direct sum of complexes of
injective objects with a common strict lower bound.** The derived functor is computed termwise
on each member of the family, by [Stacks, Tag 015E]; it is computed termwise on their direct
sum because a direct sum of injective objects is right acyclic as soon as the ordinary right
derived functors commute with it, which is the hypothesis `hsums`; and `F` itself commutes with
the direct sum, being its own zeroth right derived functor. -/
lemma preservesColimit_ofIsGE_of_injective
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived p))
    (M : I → CochainComplex A ℤ) (a : ℤ) [∀ i, (M i).IsStrictlyGE a]
    (hinj : ∀ i n, Injective ((M i).X n)) :
    PreservesColimit (Discrete.functor fun i ↦ DerivedCategory.Plus.ofIsGE (M i) a)
      F.rightDerivedFunctorPlus := by
  classical
  have hsum : (∐ M).IsStrictlyGE a := CochainComplex.isStrictlyGE_coproduct M a
  -- `F` commutes with the direct sums at issue, being its own zeroth right derived functor.
  have := hsums 0
  have hF : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  have hFM : PreservesColimitsOfShape (Discrete I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) := by
    constructor
    intro E
    constructor
    intro s hs
    refine ⟨HomologicalComplex.isColimitOfEval _ _ (fun i ↦ ?_)⟩
    have : PreservesColimit E (HomologicalComplex.eval A (ComplexShape.up ℤ) i) :=
      HomologicalComplex.instPreservesColimitEval E i
    have : PreservesColimit E (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F) :=
      comp_preservesColimit _ _
    exact isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F) hs
  -- the family and its direct sum, read in the category of bounded below complexes
  let P : I → CochainComplex.Plus A := fun i ↦ ⟨M i, a, inferInstance⟩
  let S : CochainComplex.Plus A := ⟨∐ M, a, hsum⟩
  let leg : ∀ i, P i ⟶ S := fun i ↦ ObjectProperty.homMk (Limits.Sigma.ι M i)
  let G := F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q (C := B)
  let H := DerivedCategory.Plus.Q (C := A) ⋙ F.rightDerivedFunctorPlus
  -- every term of every member of the family, and of their direct sum, is right acyclic
  have hac (i : I) (n : ℤ) : F.rightAcyclic ((M i).X n) :=
    have := hinj i n
    F.rightAcyclic_of_injective ((M i).X n)
  have hacsum (n : ℤ) : F.rightAcyclic ((∐ M).X n) := by
    have hev := isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
      (coproductIsCoproduct M)
    let e : (∐ M).X n ≅ ∐ (fun i ↦ (M i).X n) :=
      ((isColimitMapCoconeCofanMkEquiv _ _ _) hev).coconePointUniqueUpToIso
        (coproductIsCoproduct (fun i ↦ (M i).X n))
    exact ObjectProperty.prop_of_iso _ e.symm
      (Stacks.Cohomology.CompactExtensionByZero.rightAcyclic_coproduct_of_injectives F I
        (fun i ↦ (M i).X n) (fun i ↦ hinj i n) hsums)
  -- the comparison is invertible at the family and at its direct sum
  have hlegs (j : Discrete I) :
      IsIso ((Functor.mapCochainComplexPlusDerivedUnit F).app ((Discrete.functor P).obj j)) :=
    isIso_mapCochainComplexPlusDerivedUnit_app F (P j.as) (hac j.as)
  have hapex : IsIso ((Functor.mapCochainComplexPlusDerivedUnit F).app S) :=
    isIso_mapCochainComplexPlusDerivedUnit_app F S hacsum
  -- the termwise image of the cofan is a coproduct cofan
  have hFcofan : IsColimit (Cofan.mk
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∐ M))
      (fun i ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Limits.Sigma.ι M i))) :=
    isColimitMapCoconeCofanMkEquiv _ _ _
      (isColimitOfPreserves (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (coproductIsCoproduct M))
  have hGcofan : IsColimit (Cofan.mk (G.obj S) (fun i ↦ G.map (leg i))) :=
    isColimitCofanOfIsGE a ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∐ M))
      (fun i ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Limits.Sigma.ι M i)) hFcofan
  have hG : IsColimit (G.mapCocone (Cofan.mk S leg)) :=
    (isColimitMapCoconeCofanMkEquiv _ _ _).symm hGcofan
  have hH : IsColimit (H.mapCocone (Cofan.mk S leg)) :=
    isColimitMapCoconeOfIsIso (Discrete.functor P) (Cofan.mk S leg) G H
      (Functor.mapCochainComplexPlusDerivedUnit F) hlegs hapex hG
  have hHcofan : IsColimit (Cofan.mk (H.obj S) (fun i ↦ H.map (leg i))) :=
    isColimitMapCoconeCofanMkEquiv _ _ _ hH
  refine DerivedCategory.Plus.preservesColimit_termwiseDirectSum M a
    F.rightDerivedFunctorPlus ?_
  exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm hHcofan

/-- **The bounded below right derived functor of a left exact functor commutes with a direct
sum of a family admitting a common lower bound**, as soon as all the ordinary right derived
functors commute with that direct sum.

Each member of the family is replaced by a complex of injective objects that is strictly
bounded below by the same `a`, using `DerivedCategory.Plus.exists_injective_nonempty_iso`,
which is the bounded below half of [Stacks, Tag 07D9], and
`preservesColimit_ofIsGE_of_injective` applies to the replacement. -/
lemma preservesColimit_rightDerivedFunctorPlus_of_isGE
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived p))
    (K : I → DerivedCategory.Plus A) (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K) F.rightDerivedFunctorPlus := by
  classical
  have hres (i : I) : ∃ (L : CochainComplex.Plus (InjectiveObject A))
      (_ : L.obj.IsStrictlyGE a), Nonempty (DerivedCategory.Plus.Q.obj
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L) ≅ K i) :=
    have := hK i
    DerivedCategory.Plus.exists_injective_nonempty_iso (K i) a
  choose L hL hiso using hres
  have hM (i : I) : (((InjectiveObject.ι A).mapCochainComplexPlus.obj (L i)).obj).IsStrictlyGE
      a := by
    have := hL i
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj (L i).obj) a
    infer_instance
  have hinj (i : I) (n : ℤ) :
      Injective ((((InjectiveObject.ι A).mapCochainComplexPlus.obj (L i)).obj).X n) :=
    ((L i).obj.X n).property
  have hpres := preservesColimit_ofIsGE_of_injective F hsums
    (fun i ↦ ((InjectiveObject.ι A).mapCochainComplexPlus.obj (L i)).obj) a hinj
  have e : Discrete.functor (fun i ↦ DerivedCategory.Plus.ofIsGE
      ((((InjectiveObject.ι A).mapCochainComplexPlus.obj (L i)).obj)) a) ≅
      Discrete.functor K :=
    Discrete.natIso fun j ↦ (hiso j.as).some
  exact preservesColimit_of_iso_diagram F.rightDerivedFunctorPlus e

end Machinery

section Etale

variable (Λ : Type r) [Ring Λ]

/-- **Bounded below derived direct images of sheaves of `Λ`-modules commute with direct sums of
a family with a common lower bound, given [Stacks, Tag 09Z1].** Let `Λ` be a ring, let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, let
`K : I → D⁺(X_étale, Λ)` be a family of objects and let `a : ℤ` be such that `H^n(K i) = 0` for
`n < a` and all `i`, that is `(K i).IsGE a`. If each ordinary higher direct image `R^q f_*`
commutes with the direct sum (`hsums`), then `Rf_*(⨁ i, K i) = ⨁ i, Rf_*(K i)`.

The argument `hsums` is [Stacks, Tag 09Z1], proved downstream as
`preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`; the statement
without it is `preservesColimit_etaleModuleDerivedDirectImage_of_isGE_univ`. That `f_*` itself
commutes with the direct sum follows from `hsums` at `q = 0`, and the rest of the argument of
the source — the injective resolutions bounded below by `a` of [Stacks, Tag 07D9], the right
acyclicity of their termwise direct sum, and Leray's acyclicity lemma [Stacks, Tag 015E]
identifying `Rf_*` with the termwise image on each of them — is proved here.

Quasi-compactness and quasi-separatedness of `f` are the hypotheses under which [Stacks,
Tag 09Z1] holds; the argument here consumes them only through `hsums`.

The module docstring records why the statement is read on `D⁺`, and why the index universe is
`max (u + 1) r`. -/
theorem preservesColimit_etaleModuleDerivedDirectImage_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (max (u + 1) r)}
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I)
      ((etaleModuleDirectImage.{u, r} Λ f).rightDerived p))
    (K : I → DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K) (etaleModuleDerivedDirectImage.{u, r} Λ f) :=
  preservesColimit_rightDerivedFunctorPlus_of_isGE
    (etaleModuleDirectImage.{u, r} Λ f) hsums K a hK

end Etale

end Stacks.EtaleCohomology

end
