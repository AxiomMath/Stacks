module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Quasi-isomorphisms of complexes of abelian sheaves checked on enough objects

Let `C` be a site and `𝒲` a property of objects of `C` such that every object is covered by the
objects with `𝒲`: the sieve of arrows factoring through an object with `𝒲` is covering. A
morphism of presheaves of abelian groups which is bijective on the sections over every object with
`𝒲` is locally bijective, so its sheafification is an isomorphism. Consequently a morphism of
complexes of abelian sheaves is a quasi-isomorphism in degree `n` as soon as it induces
quasi-isomorphisms in degree `n` of the complexes of sections over the objects with `𝒲`: the
homology sheaves are the sheafifications of the homology presheaves, and homology of presheaves is
computed objectwise.

The typical uses are `𝒲` = the affine objects of a small étale site, and `𝒲` = the objects
mapping into some member of a covering.

## Main results

* `Stacks.Sites.isLocallyInjective_of_isIso_app` and
  `Stacks.Sites.isLocallySurjective_of_isIso_app`.
* `Stacks.Sites.isIso_sheafify_map_of_isIso_app`: the sheafification of such a morphism is an
  isomorphism.
* `Stacks.Sites.quasiIsoAt_of_quasiIsoAt_sections`: the criterion for complexes of sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (𝒲 : C → Prop)

/-- The objects with `𝒲` cover every object: the sieve of arrows factoring through an object
with `𝒲` is covering. -/
def CoversByProperty (J : GrothendieckTopology C) : Prop :=
  ∀ U : C, Sieve.generate (fun (V : C) (_ : V ⟶ U) => 𝒲 V) ∈ J U

variable {𝒲}

/-- A morphism of presheaves of abelian groups injective on the sections over enough objects is
locally injective. -/
theorem isLocallyInjective_of_isIso_app (h𝒲 : CoversByProperty 𝒲 J)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q) (hf : ∀ V, 𝒲 V → IsIso (f.app (op V))) :
    Presheaf.IsLocallyInjective J f where
  equalizerSieve_mem {U} x y hxy := by
    refine J.superset_covering ?_ (h𝒲 U.unop)
    rintro V g ⟨W, a, b, hW, rfl⟩
    have := hf W hW
    have hb : P.map b.op x = P.map b.op y := by
      apply (ConcreteCategory.bijective_of_isIso (f.app (op W))).1
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    change P.map (a ≫ b).op x = P.map (a ≫ b).op y
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hb]

/-- A morphism of presheaves of abelian groups surjective on the sections over enough objects is
locally surjective. -/
theorem isLocallySurjective_of_isIso_app (h𝒲 : CoversByProperty 𝒲 J)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q) (hf : ∀ V, 𝒲 V → IsIso (f.app (op V))) :
    Presheaf.IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (h𝒲 U)
    rintro V g ⟨W, a, b, hW, rfl⟩
    have := hf W hW
    obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (f.app (op W))).2 (Q.map b.op s)
    refine ⟨P.map a.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp_apply]

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A morphism of presheaves bijective over enough objects has invertible sheafification.** -/
theorem isIso_sheafify_map_of_isIso_app (h𝒲 : CoversByProperty 𝒲 J)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q) (hf : ∀ V, 𝒲 V → IsIso (f.app (op V))) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{w}).map f) := by
  have := isLocallyInjective_of_isIso_app h𝒲 f hf
  have := isLocallySurjective_of_isIso_app h𝒲 f hf
  exact (J.W_iff f).1 (J.W_of_isLocallyBijective f)

section Homology

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] [Abelian D₁] [Abelian D₂]

/-- For a functor preserving homology, the image of a morphism of short complexes is a
quasi-isomorphism exactly when the image of its homology map is an isomorphism. -/
theorem quasiIso_mapShortComplex_iff (F : D₁ ⥤ D₂) [F.PreservesZeroMorphisms]
    [F.PreservesHomology] {S₁ S₂ : ShortComplex D₁} (φ : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso (F.mapShortComplex.map φ) ↔
      IsIso (F.map (ShortComplex.homologyMap φ)) := by
  rw [ShortComplex.quasiIso_iff]
  have e : Arrow.mk (ShortComplex.homologyMap (F.mapShortComplex.map φ)) ≅
      Arrow.mk (F.map (ShortComplex.homologyMap φ)) :=
    Arrow.isoMk (S₁.mapHomologyIso F) (S₂.mapHomologyIso F)
      (ShortComplex.mapHomologyIso_hom_naturality φ F).symm
  exact (MorphismProperty.isomorphisms D₂).arrow_mk_iso_iff e

/-- For a functor preserving homology, the image of a morphism of complexes is a
quasi-isomorphism in degree `i` exactly when the image of its homology map in degree `i` is an
isomorphism. -/
theorem quasiIsoAt_mapHomologicalComplex_iff (F : D₁ ⥤ D₂) [F.Additive] [F.PreservesHomology]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex D₁ c} (φ : K ⟶ L) (i : ι) :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i ↔
      IsIso (F.map (HomologicalComplex.homologyMap φ i)) := by
  rw [quasiIsoAt_iff]
  exact quasiIso_mapShortComplex_iff F ((HomologicalComplex.shortComplexFunctor D₁ c i).map φ)

end Homology

/-- **Quasi-isomorphy of complexes of abelian sheaves is checked on the sections over enough
objects.** If every object of `C` is covered by objects with `𝒲`, a morphism of complexes of
abelian sheaves which induces, in degree `i`, quasi-isomorphisms of the complexes of sections over
the objects with `𝒲` is a quasi-isomorphism in degree `i`. -/
theorem quasiIsoAt_of_quasiIsoAt_sections (h𝒲 : CoversByProperty 𝒲 J)
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex (Sheaf J AddCommGrpCat.{w}) c}
    (φ : K ⟶ L) (i : ι)
    (hφ : ∀ V, 𝒲 V → QuasiIsoAt ((((sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V))).mapHomologicalComplex c).map φ) i) :
    QuasiIsoAt φ i := by
  let F := sheafToPresheaf J AddCommGrpCat.{w}
  let G := presheafToSheaf J AddCommGrpCat.{w}
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let ψ := (F.mapHomologicalComplex c).map φ
  -- the homology map of the presheaf complexes is bijective over the objects with `𝒲`
  have happ : ∀ V, 𝒲 V →
      IsIso ((HomologicalComplex.homologyMap ψ i).app (op V)) := fun V hV =>
    (quasiIsoAt_mapHomologicalComplex_iff ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op V)) ψ
      i).1 (hφ V hV)
  -- so its sheafification is a quasi-isomorphism in degree `i`
  have hGψ : QuasiIsoAt ((G.mapHomologicalComplex c).map ψ) i :=
    (quasiIsoAt_mapHomologicalComplex_iff G ψ i).2 (isIso_sheafify_map_of_isIso_app h𝒲 _ happ)
  -- and the sheafification of the presheaf complexes is the original morphism
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (HomologicalComplex (Sheaf J AddCommGrpCat.{w}) c) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{w}).symm c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  have he : Arrow.mk ((G.mapHomologicalComplex c).map ψ) ≅ Arrow.mk φ :=
    Arrow.isoMk (e.app K) (e.app L) (by simpa [ψ] using (e.hom.naturality φ).symm)
  rw [quasiIsoAt_iff] at hGψ ⊢
  exact (ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    ((HomologicalComplex.shortComplexFunctor _ c i).mapArrow.mapIso he)).1 hGψ

end Stacks.Sites

end
