module

public import Mathlib.Algebra.Category.Ring.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# Global regular functions on an algebraic space, glued from an atlas

Let `S` be a scheme in a big fppf site `B`. The ring of global regular functions on a presheaf
`F` over `S` is the ring of global sections of the structure presheaf of its small étale site,
that is, a family of regular functions on the étale scheme charts of `F` compatible with
restriction. This file shows that when `F` is an algebraic space this ring is also the ring of
compatible families of regular functions on *all* scheme charts of `F`.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctions'`: global regular functions on `F`, the sections of
  the structure presheaf of its small étale site.
* `AlgebraicGeometry.Space.chartFunctions`: families of regular functions on *all* scheme
  charts of `F`, compatible with restriction, with
  `AlgebraicGeometry.Space.chartFunctionsToSmall` the restriction to the étale charts and
  `AlgebraicGeometry.Space.chartFunctionsMap` precomposition along a morphism of presheaves.
* `AlgebraicGeometry.Space.AtlasExtensionAt`: the data extending an étale-chart section to one
  scheme chart, with `AlgebraicGeometry.Space.atlasGlobalFunctionsExtension` the resulting
  extension to every chart.
* `AlgebraicGeometry.Space.globalFunctionsChartEquiv`: the induced ring isomorphism between the
  two descriptions, and `AlgebraicGeometry.Space.globalFunctionsMap` the pullback of global
  regular functions along a morphism of algebraic spaces, packaged as the presheaf
  `AlgebraicGeometry.Space.globalFunctionsPresheaf`.

## Main results

* `AlgebraicGeometry.Space.chartFunctionsToSmall_bijective`: for an algebraic space,
  restriction from all scheme charts to the étale charts is a bijection.
* `AlgebraicGeometry.Space.isSheaf_gammaBigFppfOver`,
  `AlgebraicGeometry.Space.existsUnique_gamma_of_etale_surjection` and
  `AlgebraicGeometry.Space.gamma_injective_of_etale_surjection`: global regular functions are a
  sheaf on the big fppf site over `S`, hence descend uniquely along a surjective étale
  morphism of that site.
* `AlgebraicGeometry.Space.globalFunctionsMap_id` and
  `AlgebraicGeometry.Space.globalFunctionsMap_comp`: pullback is functorial.

## Implementation notes

`globalFunctions'`, `chartFunctions`, `chartFunctionsMap` and `chartFunctionsToSmall` are defined
for an arbitrary presheaf over `S`; `chartFunctionsToSmall_bijective` takes the algebraicity of
`F` as a hypothesis, while `globalFunctionsChartEquiv` and `globalFunctionsMap` are stated over
`AlgebraicGeometry.AlgebraicSpaces`.

## References

* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Global regular functions on the big fppf site over `S` form a sheaf of types. -/
theorem isSheaf_gammaBigFppfOver :
    Presieve.IsSheaf (BigFppfOver.topology B S hS)
      ((BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat) := by
  have h : Presheaf.IsSheaf B.topology
      (B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (B.isSheaf_globalSections)
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (Sheaf.over (⟨_, h⟩ : Sheaf B.topology (Type u)) (B.obj hS)).property

/-- A surjective étale morphism of the big fppf site over `S` generates a covering sieve. -/
theorem generate_singleton_mem_bigFppfOver_topology
    {X Y : BigFppfOver B S hS} (f : Y ⟶ X)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (he : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    Sieve.generate (Presieve.singleton f) ∈ BigFppfOver.topology B S hS X := by
  have hB : Sieve.generate (Presieve.singleton ((BigFppfOver.forget B S hS).map f)) ∈
      B.topology ((BigFppfOver.forget B S hS).obj X) :=
    B.generate_singleton_mem_topology _ hs he
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward]
  simpa [Presieve.map_singleton] using hB

/-- Global regular functions descend along a surjective étale morphism of the big fppf site. -/
theorem existsUnique_gamma_of_etale_surjection
    {X Y : BigFppfOver B S hS} (f : Y ⟶ X)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (he : Etale ((BigFppfOver.toScheme B S hS).map f))
    (s : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤))
    (hmatch : ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f →
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₁).op).hom s =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₂).op).hom s) :
    ∃! t : Γ((BigFppfOver.toScheme B S hS).obj X, ⊤),
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom t = s := by
  set Gamma := (BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat with hG
  have hsingle : Presieve.IsSheafFor Gamma (Presieve.singleton f) := by
    refine (Presieve.isSheafFor_iff_generate (P := Gamma) (Presieve.singleton f)).2 ?_
    exact isSheaf_gammaBigFppfOver B S hS _
      (generate_singleton_mem_bigFppfOver_topology B S hS f hs he)
  exact (Presieve.isSheafFor_singleton (P := Gamma) (f := f)).mp hsingle s
    (fun g₁ g₂ h => hmatch g₁ g₂ h)

/-- Pullback of global functions along a surjective étale morphism of the big fppf site over `S`
is injective. -/
theorem gamma_injective_of_etale_surjection
    {X Y : BigFppfOver B S hS} (f : Y ⟶ X)
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (he : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    Function.Injective
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom) := by
  intro s₁ s₂ h
  have hmatch : ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f →
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₁).op).hom
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom s₁) =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₂).op).hom
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom s₁) := by
    intro Z g₁ g₂ hcomp
    have hm := congrArg
      (fun k => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom s₁) hcomp
    simpa only [Functor.map_comp, op_comp, CommRingCat.comp_apply] using hm
  obtain ⟨t, ht, hu⟩ := existsUnique_gamma_of_etale_surjection B S hS f hs he
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f).op).hom s₁) hmatch
  exact (hu s₁ rfl).trans (hu s₂ h.symm).symm

/-- Pullback of global functions is contravariantly functorial. -/
theorem gamma_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (Scheme.Γ.map f.op).hom ((Scheme.Γ.map g.op).hom s) =
      (Scheme.Γ.map (f ≫ g).op).hom s := by
  change (Scheme.Γ.map g.op ≫ Scheme.Γ.map f.op).hom s = _
  rw [← Functor.map_comp, ← op_comp]

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The ring of global regular functions on `F`: the global sections of the structure presheaf
of its small étale site. -/
abbrev globalFunctions' :=
  (structurePresheaf B S hS F ⋙ forget CommRingCat.{u}).sections

/-- The presheaf of global regular functions on all scheme charts of `F`. -/
abbrev chartPresheaf : (CostructuredArrow yoneda F)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CostructuredArrow.proj yoneda F ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ.{u}

/-- Regular functions compatible on all scheme charts of `F`. -/
abbrev chartFunctions :=
  (chartPresheaf B S hS F ⋙ forget CommRingCat.{u}).sections

/-- The ring structure on compatible families of regular functions on the scheme charts of `F`,
defined pointwise. -/
instance chartFunctionsCommRing : CommRing (chartFunctions B S hS F) :=
  @Subring.toCommRing (∀ j, (chartPresheaf B S hS F).obj j) _
    (RingCat.sectionsSubring (chartPresheaf B S hS F ⋙ forget₂ CommRingCat RingCat))

/-- The ring structure on global regular functions on `F`, defined pointwise. -/
noncomputable instance globalFunctionsCommRing' : CommRing (globalFunctions' B S hS F) :=
  @Subring.toCommRing (∀ j, (structurePresheaf B S hS F).obj j) _
    (RingCat.sectionsSubring
      (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat))

/-- Precomposition of compatible functions along a morphism of presheaves. -/
def chartFunctionsMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    chartFunctions B S hS F →+* chartFunctions B S hS G where
  toFun s := ⟨fun j => s.val ((CostructuredArrow.map f).op.obj j),
    fun {j k} g => s.property ((CostructuredArrow.map f).op.map g)⟩
  map_one' := by ext j; rfl
  map_mul' := by intro a b; ext j; rfl
  map_zero' := by ext j; rfl
  map_add' := by intro a b; ext j; rfl

/-- Restriction of an all-chart family of regular functions to the étale charts. -/
noncomputable def chartFunctionsToSmall :
    chartFunctions B S hS F →+* globalFunctions' B S hS F where
  toFun s := ⟨fun j => s.val ((SmallEtale.inclusion B S hS F).op.obj j),
    fun {j k} g => s.property ((SmallEtale.inclusion B S hS F).op.map g)⟩
  map_one' := by ext j; rfl
  map_mul' := by intro a b; ext j; rfl
  map_zero' := by ext j; rfl
  map_add' := by intro a b; ext j; rfl

/-- For an algebraic space `F`, restriction from all scheme charts to the étale charts is
injective. -/
theorem chartFunctionsToSmall_injective (hF : IsAlgebraicSpace B S hS F) :
    Function.Injective (chartFunctionsToSmall B S hS F) := by
  classical
  intro s t hst
  refine Functor.sections_ext_iff.mpr ?_
  intro j
  obtain ⟨A, q, hqSurj, hqEtale⟩ := hF.exists_atlas
  let AChart : SmallEtale B S hS F := ⟨CostructuredArrow.mk q, hqEtale⟩
  obtain ⟨P, α, p, hpb⟩ := hqEtale.1 j.unop.hom
  have hαEtale : Etale ((BigFppfOver.toScheme B S hS).map α) :=
    hqEtale.2 j.unop.hom p α hpb
  have hαSurj : Surjective ((BigFppfOver.toScheme B S hS).map α) :=
    hqSurj.2 j.unop.hom p α hpb
  have hp_inj := gamma_injective_of_etale_surjection B S hS α hαSurj hαEtale
  let jA : CostructuredArrow yoneda F := CostructuredArrow.mk q
  let pHom : P ⟶ A := Yoneda.fullyFaithful.preimage p
  have hpHom : yoneda.map pHom = p := Yoneda.fullyFaithful.map_preimage p
  let jP : CostructuredArrow yoneda F := CostructuredArrow.mk (yoneda.map pHom ≫ q)
  let jW : CostructuredArrow yoneda F := j.unop
  let gAP : jP ⟶ jA := CostructuredArrow.homMk pHom (by simp [jP, jA])
  let gPW : jP ⟶ jW := CostructuredArrow.homMk α (by
    change yoneda.map α ≫ jW.hom = yoneda.map pHom ≫ q
    rw [hpHom]
    exact hpb.w.symm)
  have hA : s.val (Opposite.op jA) = t.val (Opposite.op jA) :=
    congrFun (congrArg Subtype.val hst) (Opposite.op AChart)
  have hsAP : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom
      (s.val (Opposite.op jA)) = s.val (Opposite.op jP) := s.property gAP.op
  have htAP : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom
      (t.val (Opposite.op jA)) = t.val (Opposite.op jP) := t.property gAP.op
  have hsPW : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom
      (s.val (Opposite.op jW)) = s.val (Opposite.op jP) := s.property gPW.op
  have htPW : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom
      (t.val (Opposite.op jW)) = t.val (Opposite.op jP) := t.property gPW.op
  refine hp_inj ?_
  rw [hsPW, htPW, ← hsAP, ← htAP, hA]

/-- The value of an étale-chart section pulled back to a chosen atlas base change does not
depend on which of two parallel maps into it is used. -/
theorem atlasPullback_sections_match
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    (hqEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (s : globalFunctions' B S hS F)
    {j : CostructuredArrow yoneda F} {P : BigFppfOver B S hS}
    (α : P ⟶ j.left) (p : yoneda.obj P ⟶ yoneda.obj A)
    (hpb : IsPullback p (yoneda.map α) q j.hom)
    (pHom : P ⟶ A) (hpHom : yoneda.map pHom = p) :
    ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ P), g₁ ≫ α = g₂ ≫ α →
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (g₁ ≫ pHom)).op).hom
          (s.val (Opposite.op (⟨CostructuredArrow.mk q, hqEtale⟩ : SmallEtale B S hS F))) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (g₂ ≫ pHom)).op).hom
          (s.val (Opposite.op (⟨CostructuredArrow.mk q, hqEtale⟩ : SmallEtale B S hS F))) := by
  classical
  let Tscheme := BigFppfOver.toScheme B S hS
  let AChart : SmallEtale B S hS F := ⟨CostructuredArrow.mk q, hqEtale⟩
  obtain ⟨R, β, r, hR⟩ := hqEtale.1 q
  have hβEtale : Etale (Tscheme.map β) := hqEtale.2 q r β hR
  have hRChart' : IsEtaleChart B S hS F (CostructuredArrow.mk (yoneda.map β ≫ q)) :=
    etale_comp_of_scheme B S hS β q hβEtale hqEtale
  let RChart : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (r ≫ q), by simpa [hR.w] using hRChart'⟩
  let rHom : R ⟶ A := Yoneda.fullyFaithful.preimage r
  have hrHom : yoneda.map rHom = r := Yoneda.fullyFaithful.map_preimage r
  let gR₁ : RChart ⟶ AChart := ObjectProperty.homMk <|
    CostructuredArrow.homMk rHom (by
      change yoneda.map rHom ≫ q = r ≫ q
      rw [hrHom])
  let gR₂ : RChart ⟶ AChart := ObjectProperty.homMk <| CostructuredArrow.homMk β hR.w.symm
  have hsR₁ : (Scheme.Γ.map (Tscheme.map rHom).op).hom
      (s.val (Opposite.op AChart)) = s.val (Opposite.op RChart) := by
    convert s.property gR₁.op using 1
    rfl
  have hsR₂ : (Scheme.Γ.map (Tscheme.map β).op).hom
      (s.val (Opposite.op AChart)) = s.val (Opposite.op RChart) := by
    convert s.property gR₂.op using 1
    rfl
  intro Z g₁ g₂ h
  have hqeq : yoneda.map (g₁ ≫ pHom) ≫ q = yoneda.map (g₂ ≫ pHom) ≫ q := by
    simp only [Functor.map_comp, Category.assoc, hpHom, hpb.w]
    rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]
  let d : yoneda.obj Z ⟶ yoneda.obj R :=
    hR.lift (yoneda.map (g₁ ≫ pHom)) (yoneda.map (g₂ ≫ pHom)) hqeq
  have hd₁ : d ≫ r = yoneda.map (g₁ ≫ pHom) := hR.lift_fst _ _ hqeq
  have hd₂ : d ≫ yoneda.map β = yoneda.map (g₂ ≫ pHom) := hR.lift_snd _ _ hqeq
  let dHom : Z ⟶ R := Yoneda.fullyFaithful.preimage d
  have hdHom : yoneda.map dHom = d := Yoneda.fullyFaithful.map_preimage d
  have hcomp₁ : dHom ≫ rHom = g₁ ≫ pHom := by
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, hdHom, hrHom, hd₁]
  have hcomp₂ : dHom ≫ β = g₂ ≫ pHom := by
    apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, hdHom, hd₂]
  calc (Scheme.Γ.map (Tscheme.map (g₁ ≫ pHom)).op).hom (s.val (Opposite.op AChart))
      = (Scheme.Γ.map (Tscheme.map (dHom ≫ rHom)).op).hom
          (s.val (Opposite.op AChart)) := by rw [hcomp₁]
    _ = (Scheme.Γ.map (Tscheme.map dHom).op).hom (s.val (Opposite.op RChart)) := by
        rw [Functor.map_comp]
        exact (gamma_map_comp (Tscheme.map dHom) (Tscheme.map rHom) _).symm.trans
          (congrArg ((Scheme.Γ.map (Tscheme.map dHom).op).hom) hsR₁)
    _ = (Scheme.Γ.map (Tscheme.map (dHom ≫ β)).op).hom
          (s.val (Opposite.op AChart)) := by
        rw [Functor.map_comp]
        exact (congrArg ((Scheme.Γ.map (Tscheme.map dHom).op).hom) hsR₂.symm).trans
          (gamma_map_comp (Tscheme.map dHom) (Tscheme.map β) _)
    _ = (Scheme.Γ.map (Tscheme.map (g₂ ≫ pHom)).op).hom
          (s.val (Opposite.op AChart)) := by rw [hcomp₂]

/-- The data extending an étale-chart section of `F` to one scheme chart `j`: a base change of
the atlas over `j`, and a global function on `j` restricting to the section on it. -/
structure AtlasExtensionAt
    (c : SmallEtale B S hS F) (s : globalFunctions' B S hS F)
    (j : CostructuredArrow yoneda F) where
  /-- The base change of the atlas along the chart `j`. -/
  P : BigFppfOver B S hS
  /-- Its projection to `j`, a surjective étale morphism. -/
  α : P ⟶ j.left
  /-- Its projection to the atlas, as a map of presheaves. -/
  p : yoneda.obj P ⟶ yoneda.obj c.1.left
  /-- Its projection to the atlas, as a morphism of the site. -/
  pHom : P ⟶ c.1.left
  /-- The two readings of the projection to the atlas agree. -/
  hpHom : yoneda.map pHom = p
  /-- The defining pullback square. -/
  hpb : IsPullback p (yoneda.map α) c.1.hom j.hom
  /-- The projection to `j` is étale. -/
  hαEtale : Etale ((BigFppfOver.toScheme B S hS).map α)
  /-- The projection to `j` is surjective. -/
  hαSurj : Surjective ((BigFppfOver.toScheme B S hS).map α)
  /-- The extended global function on `j`. -/
  value : Γ((BigFppfOver.toScheme B S hS).obj j.left, ⊤)
  /-- It restricts along `α` to the section's value on the atlas chart. -/
  value_spec :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom value =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom (s.val (Opposite.op c))

/-- Given an étale atlas `q` of `F` and a section `s` on the étale charts, an extension of `s` to
the scheme chart `j` along `q` exists. -/
theorem atlas_extension_at_nonempty
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    (hqSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (s : globalFunctions' B S hS F) (j : CostructuredArrow yoneda F) :
    Nonempty (AtlasExtensionAt B S hS F ⟨CostructuredArrow.mk q, hqEtale⟩ s j) := by
  classical
  obtain ⟨P, α, p, hpb⟩ := hqEtale.1 j.hom
  have hαEtale : Etale ((BigFppfOver.toScheme B S hS).map α) := hqEtale.2 j.hom p α hpb
  have hαSurj : Surjective ((BigFppfOver.toScheme B S hS).map α) := hqSurj.2 j.hom p α hpb
  let pHom := Yoneda.fullyFaithful.preimage p
  have hpHom : yoneda.map pHom = p := Yoneda.fullyFaithful.map_preimage p
  obtain ⟨t, ht, _hu⟩ := existsUnique_gamma_of_etale_surjection B S hS α hαSurj hαEtale
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom
      (s.val (Opposite.op (⟨CostructuredArrow.mk q, hqEtale⟩ : SmallEtale B S hS F)))) (by
      intro Z g₁ g₂ h
      have hm := atlasPullback_sections_match B S hS F A q hqEtale s α p hpb pHom hpHom g₁ g₂ h
      simp only [Functor.map_comp, op_comp] at hm
      exact hm)
  exact ⟨⟨P, α, p, pHom, hpHom, hpb, hαEtale, hαSurj, t, ht⟩⟩

/-- A choice of such an extension at every scheme chart. -/
noncomputable def atlasExtensionAt
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    (hqSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (s : globalFunctions' B S hS F) (j : CostructuredArrow yoneda F) :
    AtlasExtensionAt B S hS F ⟨CostructuredArrow.mk q, hqEtale⟩ s j :=
  Classical.choice (atlas_extension_at_nonempty B S hS F A q hqSurj hqEtale s j)

/-- Two chosen atlas base changes over comparable charts are themselves comparable. -/
theorem atlas_extension_pullback_maps
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    {j k : CostructuredArrow yoneda F} (f : j ⟶ k)
    {Pj Pk : BigFppfOver B S hS} (αj : Pj ⟶ j.left) (αk : Pk ⟶ k.left)
    (pj : yoneda.obj Pj ⟶ yoneda.obj A) (pk : yoneda.obj Pk ⟶ yoneda.obj A)
    (pjHom : Pj ⟶ A) (pkHom : Pk ⟶ A)
    (hpjHom : yoneda.map pjHom = pj) (hpkHom : yoneda.map pkHom = pk)
    (hpbj : IsPullback pj (yoneda.map αj) q j.hom)
    (hpbk : IsPullback pk (yoneda.map αk) q k.hom) :
    ∃ d : Pj ⟶ Pk, d ≫ pkHom = pjHom ∧ d ≫ αk = αj ≫ f.left := by
  classical
  have hf : yoneda.map f.left ≫ k.hom = j.hom := by simp
  have hcomm : pj ≫ q = yoneda.map (αj ≫ f.left) ≫ k.hom := by
    rw [hpbj.w, ← hf, Functor.map_comp, Category.assoc]
  let dNat := hpbk.lift pj (yoneda.map (αj ≫ f.left)) hcomm
  let d := Yoneda.fullyFaithful.preimage dNat
  have hdNatP : dNat ≫ pk = pj := hpbk.lift_fst _ _ hcomm
  have hdNatAlpha : dNat ≫ yoneda.map αk = yoneda.map (αj ≫ f.left) :=
    hpbk.lift_snd _ _ hcomm
  have hdMap : yoneda.map d = dNat := Yoneda.fullyFaithful.map_preimage dNat
  have hdP : d ≫ pkHom = pjHom := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hdMap, hpkHom, hpjHom, hdNatP])
  have hdAlpha : d ≫ αk = αj ≫ f.left := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, hdMap, hdNatAlpha])
  exact ⟨d, hdP, hdAlpha⟩

/-- The extended values are compatible with restriction along a morphism of charts. -/
theorem atlas_extension_gamma_compatible
    (A : BigFppfOver B S hS) {j k : CostructuredArrow yoneda F} (f : j ⟶ k)
    {Pj Pk : BigFppfOver B S hS} (αj : Pj ⟶ j.left) (αk : Pk ⟶ k.left)
    (pjHom : Pj ⟶ A) (pkHom : Pk ⟶ A)
    (d : Pj ⟶ Pk) (hdP : d ≫ pkHom = pjHom) (hdAlpha : d ≫ αk = αj ≫ f.left)
    (hαjEtale : Etale ((BigFppfOver.toScheme B S hS).map αj))
    (hαjSurj : Surjective ((BigFppfOver.toScheme B S hS).map αj))
    (sA : Γ((BigFppfOver.toScheme B S hS).obj A, ⊤))
    (vj : Γ((BigFppfOver.toScheme B S hS).obj j.left, ⊤))
    (vk : Γ((BigFppfOver.toScheme B S hS).obj k.left, ⊤))
    (hvj : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map αj).op).hom vj =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pjHom).op).hom sA)
    (hvk : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map αk).op).hom vk =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pkHom).op).hom sA) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f.left).op).hom vk = vj := by
  classical
  let Tscheme := BigFppfOver.toScheme B S hS
  refine gamma_injective_of_etale_surjection B S hS αj hαjSurj hαjEtale ?_
  calc (Scheme.Γ.map (Tscheme.map αj).op).hom
          ((Scheme.Γ.map (Tscheme.map f.left).op).hom vk)
      = (Scheme.Γ.map (Tscheme.map (αj ≫ f.left)).op).hom vk := by
        simp only [Functor.map_comp]
        exact gamma_map_comp (Tscheme.map αj) (Tscheme.map f.left) vk
    _ = (Scheme.Γ.map (Tscheme.map (d ≫ αk)).op).hom vk := by rw [hdAlpha]
    _ = (Scheme.Γ.map (Tscheme.map d).op).hom
          ((Scheme.Γ.map (Tscheme.map αk).op).hom vk) := by
        simpa only [Functor.map_comp] using
          (gamma_map_comp (Tscheme.map d) (Tscheme.map αk) vk).symm
    _ = (Scheme.Γ.map (Tscheme.map d).op).hom
          ((Scheme.Γ.map (Tscheme.map pkHom).op).hom sA) :=
        congrArg ((Scheme.Γ.map (Tscheme.map d).op).hom) hvk
    _ = (Scheme.Γ.map (Tscheme.map (d ≫ pkHom)).op).hom sA := by
        simpa only [Functor.map_comp] using
          gamma_map_comp (Tscheme.map d) (Tscheme.map pkHom) sA
    _ = (Scheme.Γ.map (Tscheme.map pjHom).op).hom sA := by rw [hdP]
    _ = (Scheme.Γ.map (Tscheme.map αj).op).hom vj := hvj.symm

/-- On an étale chart the extension returns the section's own value there. -/
theorem atlas_extension_restrict_small
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    (hqSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (s : globalFunctions' B S hS F) (c : SmallEtale B S hS F) :
    (atlasExtensionAt B S hS F A q hqSurj hqEtale s c.1).value = s.val (Opposite.op c) := by
  classical
  let Tscheme := BigFppfOver.toScheme B S hS
  let ext := atlasExtensionAt B S hS F A q hqSurj hqEtale s c.1
  let AChart : SmallEtale B S hS F := ⟨CostructuredArrow.mk q, hqEtale⟩
  have hpb' : IsPullback (yoneda.map ext.pHom) (yoneda.map ext.α) q c.1.hom := by
    rw [ext.hpHom]; exact ext.hpb
  have hpEtale : Etale (Tscheme.map ext.pHom) :=
    c.property.2 q (yoneda.map ext.α) ext.pHom hpb'.flip
  have hPChart' : IsEtaleChart B S hS F
      (CostructuredArrow.mk (yoneda.map ext.pHom ≫ q)) :=
    etale_comp_of_scheme B S hS ext.pHom q hpEtale hqEtale
  let PChart : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map ext.pHom ≫ q), hPChart'⟩
  let hα : PChart ⟶ c := ObjectProperty.homMk <|
    CostructuredArrow.homMk ext.α (by
      change yoneda.map ext.α ≫ c.1.hom = yoneda.map ext.pHom ≫ q
      rw [ext.hpHom]; exact ext.hpb.w.symm)
  let hp : PChart ⟶ AChart := ObjectProperty.homMk <| CostructuredArrow.homMk ext.pHom rfl
  have hsα : (Scheme.Γ.map (Tscheme.map ext.α).op).hom (s.val (Opposite.op c)) =
      s.val (Opposite.op PChart) := s.property hα.op
  have hsp : (Scheme.Γ.map (Tscheme.map ext.pHom).op).hom (s.val (Opposite.op AChart)) =
      s.val (Opposite.op PChart) := s.property hp.op
  refine gamma_injective_of_etale_surjection B S hS ext.α ext.hαSurj ext.hαEtale ?_
  have hval : (Scheme.Γ.map (Tscheme.map ext.α).op).hom ext.value =
      (Scheme.Γ.map (Tscheme.map ext.pHom).op).hom (s.val (Opposite.op AChart)) := by
    simpa [AChart, Tscheme, BigFppfOver.toScheme] using ext.value_spec
  exact hval.trans hsp |>.trans hsα.symm

/-- Extension of an étale-chart family of regular functions to all scheme charts, along a
chosen atlas. -/
noncomputable def atlasGlobalFunctionsExtension
    (A : BigFppfOver B S hS) (q : yoneda.obj A ⟶ F)
    (hqSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (s : globalFunctions' B S hS F) : chartFunctions B S hS F := by
  classical
  let c : SmallEtale B S hS F := ⟨CostructuredArrow.mk q, hqEtale⟩
  refine ⟨fun j => (atlasExtensionAt B S hS F A q hqSurj hqEtale s j.unop).value, ?_⟩
  intro j k f
  let ej := atlasExtensionAt B S hS F A q hqSurj hqEtale s k.unop
  let ek := atlasExtensionAt B S hS F A q hqSurj hqEtale s j.unop
  obtain ⟨d, hdP, hdAlpha⟩ := atlas_extension_pullback_maps B S hS F A q f.unop
    ej.α ek.α ej.p ek.p ej.pHom ek.pHom ej.hpHom ek.hpHom ej.hpb ek.hpb
  exact atlas_extension_gamma_compatible B S hS F A f.unop ej.α ek.α ej.pHom ek.pHom
    d hdP hdAlpha ej.hαEtale ej.hαSurj (s.val (Opposite.op c)) ej.value ek.value
    ej.value_spec ek.value_spec

/-- Restriction to the étale charts is surjective: every étale-chart family of regular
functions extends to all scheme charts along an atlas. -/
theorem chartFunctionsToSmall_surjective (hF : IsAlgebraicSpace B S hS F) :
    Function.Surjective (chartFunctionsToSmall B S hS F) := by
  classical
  intro s
  obtain ⟨A, q, hqSurj, hqEtale⟩ := hF.exists_atlas
  refine ⟨atlasGlobalFunctionsExtension B S hS F A q hqSurj hqEtale s, ?_⟩
  ext c
  exact atlas_extension_restrict_small B S hS F A q hqSurj hqEtale s c.unop

/-- For an algebraic space `F`, restriction to the étale charts is a bijection: a compatible
family of regular functions on all scheme charts of `F` is the same thing as a global section of
its small étale structure sheaf. -/
theorem chartFunctionsToSmall_bijective (hF : IsAlgebraicSpace B S hS F) :
    Function.Bijective (chartFunctionsToSmall B S hS F) :=
  ⟨chartFunctionsToSmall_injective B S hS F hF, chartFunctionsToSmall_surjective B S hS F hF⟩

/-- The induced ring isomorphism between global functions on an algebraic space and compatible
families of regular functions on all of its scheme charts, together with the fact that it is
inverse to restriction. -/
noncomputable def globalFunctionsChartEquiv (U : AlgebraicSpaces B S hS) :
    {e : globalFunctions' B S hS U.1 ≃+* chartFunctions B S hS U.1 //
      ∀ s, chartFunctionsToSmall B S hS U.1 (e s) = s} :=
  ⟨(RingEquiv.ofBijective _ (chartFunctionsToSmall_bijective B S hS U.1 U.property)).symm,
    fun s => (RingEquiv.ofBijective _
      (chartFunctionsToSmall_bijective B S hS U.1 U.property)).apply_symm_apply s⟩

/-- Pullback of global regular functions along a morphism of algebraic spaces: on all scheme
charts it is precomposition. -/
noncomputable def globalFunctionsMap {U V : AlgebraicSpaces B S hS} (f : V ⟶ U) :
    globalFunctions' B S hS U.1 →+* globalFunctions' B S hS V.1 :=
  (globalFunctionsChartEquiv B S hS V).val.symm.toRingHom.comp
    ((chartFunctionsMap B S hS f.hom).comp (globalFunctionsChartEquiv B S hS U).val.toRingHom)

/-- Pullback of global functions is characterised by precomposition on all scheme charts. -/
theorem globalFunctionsMap_chart {U V : AlgebraicSpaces B S hS} (f : V ⟶ U)
    (s : globalFunctions' B S hS U.1) :
    (globalFunctionsChartEquiv B S hS V).val (globalFunctionsMap B S hS f s) =
      chartFunctionsMap B S hS f.hom ((globalFunctionsChartEquiv B S hS U).val s) :=
  (globalFunctionsChartEquiv B S hS V).val.apply_symm_apply _

/-- Pullback of global regular functions along the identity is the identity. -/
@[simp] theorem globalFunctionsMap_id (U : AlgebraicSpaces B S hS) :
    globalFunctionsMap B S hS (𝟙 U) = RingHom.id (globalFunctions' B S hS U.1) := by
  refine RingHom.ext fun s => ?_
  refine (globalFunctionsChartEquiv B S hS U).val.injective ?_
  rw [globalFunctionsMap_chart]
  ext j
  rfl

/-- Pullback of global regular functions along a composite is the composite of the pullbacks. -/
theorem globalFunctionsMap_comp {U V W : AlgebraicSpaces B S hS} (f : W ⟶ V) (g : V ⟶ U) :
    globalFunctionsMap B S hS (f ≫ g) =
      (globalFunctionsMap B S hS f).comp (globalFunctionsMap B S hS g) := by
  refine RingHom.ext fun s => ?_
  refine (globalFunctionsChartEquiv B S hS W).val.injective ?_
  rw [globalFunctionsMap_chart, RingHom.comp_apply, globalFunctionsMap_chart,
    globalFunctionsMap_chart]
  ext j
  rfl

/-- The presheaf of global regular functions on algebraic spaces over `S`. -/
noncomputable def globalFunctionsPresheaf :
    (AlgebraicSpaces B S hS)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (globalFunctions' B S hS U.unop.1)
  map f := CommRingCat.ofHom (globalFunctionsMap B S hS f.unop)
  map_id U := CommRingCat.hom_ext (globalFunctionsMap_id B S hS U.unop)
  map_comp f g := CommRingCat.hom_ext (globalFunctionsMap_comp B S hS g.unop f.unop)

end AlgebraicGeometry.Space

end
