module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent modules on a coproduct of schemes are the product over the summands

Sheaves of modules are additive over a coproduct of schemes: a quasi-coherent descent datum for a
family `{X i ⟶ T}` is effective on the covering of `∐ X i` by its summands, and morphisms of
sheaves of modules on `∐ X i` are the same thing as unrestricted families of morphisms of their
restrictions to the summands. Both hold for an arbitrary (`Small`) index type and with no
hypothesis on the schemes involved. As a consequence, quasi-coherent descent data for
`{X i ⟶ T}` and for the one-element family `{∐ X i ⟶ T}` agree, which gives the effectivity half
of [Stacks, Tag 023S] and of [Stacks, Tag 023T] over a spectrum.

## Main definitions

* `AlgebraicGeometry.restrictToSummands`: a quasi-coherent descent datum for a family
  `{X i ⟶ T}`, read as a quasi-coherent descent datum for the covering of `∐ X i` by its
  summands.
* `AlgebraicGeometry.disjointCoverDescentHom` and `AlgebraicGeometry.summandDescentHom`: a bare
  family of morphisms of the restrictions is a morphism of descent data, for an open covering with
  no overlaps and for the summand covering of a coproduct respectively.
* `AlgebraicGeometry.refineCover`: the refinement of an open covering making a given morphism
  factor through the members of a covering of its target.
* `AlgebraicGeometry.summandTransition` and `AlgebraicGeometry.sigmaTransition`: the transition
  of the coproduct datum at a pair of morphisms factoring through summands, and at an arbitrary
  pair of morphisms to the coproduct over the base.
* `AlgebraicGeometry.QuasicoherentDescentData.ofSummands`: the quasi-coherent descent datum for
  the one-element family `{∐ X i ⟶ T}` built from a datum for `{X i ⟶ T}`, with its comparison
  isomorphism `AlgebraicGeometry.QuasicoherentDescentData.ofSummandsIso`.

## Main results

* `AlgebraicGeometry.subsingleton_hom_of_isEmpty`: a scheme with no points carries exactly one
  morphism between any two of its sheaves of modules.
* `AlgebraicGeometry.isEffective_restrictToSummands`: for every family `f i : X i ⟶ T` and every
  quasi-coherent descent datum `D` for it, the induced datum for the summand covering of `∐ X i`
  is effective.
* `AlgebraicGeometry.exists_hom_of_disjointCoverHoms` and
  `AlgebraicGeometry.injective_map_openCover`: morphisms of sheaves of modules descend along an
  open covering with no overlaps, with no compatibility condition on the family, and are
  determined by their restrictions to the members of any open covering.
* `AlgebraicGeometry.exists_hom_of_summandHoms`, `AlgebraicGeometry.injective_map_sigmaι` and
  `AlgebraicGeometry.bijective_map_sigmaι`: restriction to the summands is a bijection from the
  morphisms of two sheaves of modules on `∐ Z k` onto the unrestricted families of morphisms of
  their restrictions.
* `AlgebraicGeometry.QuasicoherentDescentData.essSurj_pullFunctor_toSigmaFamily`: restriction of
  quasi-coherent descent data along the coproduct refinement is essentially surjective.
* `AlgebraicGeometry.QuasicoherentDescentData.standardSigmaEssSurj`: the hypothesis
  `StandardSigmaEssSurj` holds.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc` and
  `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_spec`: quasi-coherent
  descent data for a standard fpqc covering, and for an arbitrary fpqc covering, of `Spec R` are
  effective.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage_of_globalizes`: over an
  arbitrary base, quasi-coherent descent data for an fpqc covering are effective under
  `AlgebraicGeometry.QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes`.

## Implementation notes

`AlgebraicGeometry.restrictToSummands` is written directly as a descent datum rather than as
`AlgebraicGeometry.QuasicoherentDescentData.pullFunctor` along `Sigma.desc`, so that its
component sheaves are equal, not merely isomorphic, to those of `D`.

The morphism half is proved for an arbitrary open covering with no overlaps, since the pullback
of the summand covering along a morphism into the coproduct is not a coproduct decomposition on
the nose.

In the quasi-inverse every step is a `pullHom` of a fixed morphism, never an `inv` or an
`eqToHom`, and both directions of the comparison at a summand are written out, so that rewriting
under them never meets an instance-dependent motive. The two arguments `u v : V ⟶ ∐ X` of a
transition are carried in its type, so that two factorizations of one pair give morphisms of the
same type.

The `Subsingleton` instance on morphisms over an empty scheme is needed at the pullback
pseudofunctor's spelling of the category of sheaves of modules as well as at
`AlgebraicGeometry.Scheme.Modules` (`AlgebraicGeometry.subsingleton_hom_pseudofunctor`): instance
synthesis does not cross that spelling.

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {I : Type w} [Small.{u} I] {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}

/-- A morphism into a summand of a coproduct which lies over a morphism to the coproduct lies,
after composition with the coproduct morphism, over the corresponding morphism to the base. -/
public theorem comp_desc_of_comp_sigmaι {Y : Scheme.{u}} {q : Y ⟶ ∐ X} {i : I} {g : Y ⟶ X i}
    (hg : g ≫ Sigma.ι X i = q) : g ≫ f i = q ≫ Sigma.desc f := by
  rw [← hg, ← Sigma.ι_comp_desc f i, Category.assoc]

/-- A quasi-coherent descent datum for a family `{X i ⟶ T}`, read as one for the covering of
`∐ X i` by its summands. The component sheaves are unchanged, and the transition over a morphism
`q : Y ⟶ ∐ X i` with factorizations through two summands is the transition of the original datum
over `q ≫ (∐ X i ⟶ T)`. -/
public noncomputable def restrictToSummands (D : QuasicoherentDescentData f) :
    QuasicoherentDescentData (fun i ↦ Sigma.ι X i) where
  obj :=
  { obj := D.obj.obj
    hom _ q _ _ f₁ f₂ hf₁ hf₂ := D.obj.hom (q ≫ Sigma.desc f) f₁ f₂
      (comp_desc_of_comp_sigmaι hf₁) (comp_desc_of_comp_sigmaι hf₂)
    pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
      D.obj.pullHom_hom g (q ≫ Sigma.desc f) (q' ≫ Sigma.desc f) (by rw [← hq]; simp)
        f₁ f₂ (comp_desc_of_comp_sigmaι hf₁) (comp_desc_of_comp_sigmaι hf₂) gf₁ gf₂ hgf₁ hgf₂
    hom_self _ q _ g hg := D.obj.hom_self (q ≫ Sigma.desc f) g (comp_desc_of_comp_sigmaι hg)
    hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
      D.obj.hom_comp (q ≫ Sigma.desc f) f₁ f₂ f₃ (comp_desc_of_comp_sigmaι hf₁)
        (comp_desc_of_comp_sigmaι hf₂) (comp_desc_of_comp_sigmaι hf₃) }
  property := D.property

/-- The component sheaves of `AlgebraicGeometry.restrictToSummands` are those of the given datum.
-/
public theorem restrictToSummands_component (D : QuasicoherentDescentData f) (i : I) :
    (restrictToSummands D).component i = D.component i := rfl

/-- For every family `f i : X i ⟶ T` and every quasi-coherent descent datum `D` for it, the datum
`AlgebraicGeometry.restrictToSummands D` for the covering of `∐ X i` by its summands is effective:
there is a quasi-coherent module on `∐ X i` restricting on each summand to `D.component i`,
compatibly with every transition of `D`. -/
public theorem isEffective_restrictToSummands (D : QuasicoherentDescentData f) :
    (restrictToSummands D).IsEffective :=
  Stacks.Descent.isEffective_zariski (fun i ↦ Sigma.ι X i) (sigmaOpenCover X).iSup_opensRange _

/-- A sheaf of modules on a scheme with no points has only the zero section over any open, the ring
of functions there being the zero ring. -/
public theorem subsingleton_sections_of_isEmpty {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    [IsEmpty Y] : Subsingleton Γ(M, U) := by
  have h : (0 : Γ(Y, U)) = 1 := Subsingleton.elim _ _
  refine ⟨fun x y ↦ ?_⟩
  have hz (z : Γ(M, U)) : z = 0 := by
    rw [← one_smul Γ(Y, U) z, ← h, zero_smul]
  exact (hz x).trans (hz y).symm

/-- A scheme with no points carries exactly one morphism between any two of its sheaves of modules.
-/
public instance subsingleton_hom_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M N : Y.Modules) :
    Subsingleton (M ⟶ N) := by
  refine ⟨fun a b ↦ Scheme.Modules.hom_ext _ _ fun U ↦ ?_⟩
  have := subsingleton_sections_of_isEmpty N U
  ext x
  exact Subsingleton.elim _ _

/-- `AlgebraicGeometry.subsingleton_hom_of_isEmpty` at the pullback pseudofunctor's spelling of the
category of sheaves of modules. -/
public theorem subsingleton_hom_pseudofunctor {Y : Scheme.{u}} [IsEmpty Y]
    (M N : modulePullbackPseudofunctor.obj (.mk (op Y))) : Subsingleton (M ⟶ N) :=
  subsingleton_hom_of_isEmpty M N

/-- For sheaves of modules `A` and `B` on a scheme `Y` and an open covering of `Y` any two distinct
members of which receive a common morphism only from an empty scheme, an arbitrary family of
morphisms of the restrictions of `A` and `B` to the members satisfies the compatibility condition
required of a morphism of descent data. -/
public noncomputable def disjointCoverDescentHom {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (hdisj : ∀ k l, k ≠ l → ∀ {V : Scheme.{u}} (a : V ⟶ 𝒰.X k) (b : V ⟶ 𝒰.X l),
      a ≫ 𝒰.f k = b ≫ 𝒰.f l → IsEmpty V)
    (A B : Y.Modules)
    (φ : ∀ k, (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.obj A ⟶
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.obj B) :
    (modulePullbackPseudofunctor.toDescentData 𝒰.f).obj A ⟶
      (modulePullbackPseudofunctor.toDescentData 𝒰.f).obj B where
  hom := φ
  comm V q k₁ k₂ f₁ f₂ hf₁ hf₂ := by
    by_cases hk : k₁ = k₂
    · subst hk
      obtain rfl : f₁ = f₂ := (cancel_mono (𝒰.f k₁)).mp (by rw [hf₁, hf₂])
      rw [Pseudofunctor.DescentData.hom_self _ q f₁ hf₁,
        Pseudofunctor.DescentData.hom_self _ q f₁ hf₁]
      simp
    · have : IsEmpty V := hdisj k₁ k₂ hk f₁ f₂ (hf₁.trans hf₂.symm)
      exact @Subsingleton.elim _ (subsingleton_hom_pseudofunctor _ _) _ _

/-- Every family of morphisms of the restrictions of two sheaves of modules to the members of such
a covering is the restriction of a morphism on the base. -/
public theorem exists_hom_of_disjointCoverHoms {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (hdisj : ∀ k l, k ≠ l → ∀ {V : Scheme.{u}} (a : V ⟶ 𝒰.X k) (b : V ⟶ 𝒰.X l),
      a ≫ 𝒰.f k = b ≫ 𝒰.f l → IsEmpty V)
    (A B : Y.Modules)
    (φ : ∀ k, (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.obj A ⟶
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.obj B) :
    ∃ ψ : A ⟶ B, ∀ k,
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.map ψ = φ k := by
  let ff := Pseudofunctor.fullyFaithfulToDescentData modulePullbackPseudofunctor
    (J := Scheme.zariskiTopology.{u}) (f := 𝒰.f) 𝒰.mem_grothendieckTopology
  refine ⟨ff.preimage (disjointCoverDescentHom 𝒰 hdisj A B φ), fun k ↦ ?_⟩
  have := ff.map_preimage (disjointCoverDescentHom 𝒰 hdisj A B φ)
  exact congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η k) this

/-- A morphism of sheaves of modules is determined by its restrictions to the members of an open
covering. -/
public theorem injective_map_openCover {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (A B : Y.Modules) :
    Function.Injective (fun (ψ : A ⟶ B) k ↦
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.map ψ) := by
  intro ψ ψ' h
  let ff := Pseudofunctor.fullyFaithfulToDescentData modulePullbackPseudofunctor
    (J := Scheme.zariskiTopology.{u}) (f := 𝒰.f) 𝒰.mem_grothendieckTopology
  exact ff.map_injective (Pseudofunctor.DescentData.hom_ext (fun k ↦ congrFun h k))

variable {Z : I → Scheme.{u}}

/-- The covering of a coproduct of schemes by its summands generates a Zariski covering sieve. -/
public theorem sigmaι_mem_zariskiTopology :
    Sieve.ofArrows Z (fun k ↦ Sigma.ι Z k) ∈ Scheme.zariskiTopology.{u} (∐ Z) :=
  (sigmaOpenCover Z).mem_grothendieckTopology

/-- Two distinct summands of a coproduct of schemes receive a common morphism only from a scheme
with no points. -/
public theorem isEmpty_of_comp_sigmaOpenCover_eq (k l : I) (hkl : k ≠ l) {V : Scheme.{u}}
    (a : V ⟶ (sigmaOpenCover Z).X k) (b : V ⟶ (sigmaOpenCover Z).X l)
    (hab : a ≫ (sigmaOpenCover Z).f k = b ≫ (sigmaOpenCover Z).f l) : IsEmpty V :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨hab⟩ hkl

/-- Over a coproduct of schemes, a bare family of morphisms of the restrictions to the summands is
a morphism of descent data for the summand covering. -/
public noncomputable def summandDescentHom (A B : (∐ Z).Modules)
    (φ : ∀ k, (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.obj A ⟶
      (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.obj B) :
    (modulePullbackPseudofunctor.toDescentData (fun k ↦ Sigma.ι Z k)).obj A ⟶
      (modulePullbackPseudofunctor.toDescentData (fun k ↦ Sigma.ι Z k)).obj B :=
  have : Small.{u} (sigmaOpenCover Z).I₀ := ‹Small.{u} I›
  disjointCoverDescentHom (sigmaOpenCover Z) isEmpty_of_comp_sigmaOpenCover_eq A B φ

/-- Every family of morphisms of the restrictions of two sheaves of modules on `∐ Z k` to the
summands — with no compatibility condition imposed — is the restriction of a morphism on `∐ Z k`.
-/
public theorem exists_hom_of_summandHoms (A B : (∐ Z).Modules)
    (φ : ∀ k, (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.obj A ⟶
      (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.obj B) :
    ∃ ψ : A ⟶ B, ∀ k,
      (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.map ψ = φ k :=
  have : Small.{u} (sigmaOpenCover Z).I₀ := ‹Small.{u} I›
  exists_hom_of_disjointCoverHoms (sigmaOpenCover Z) isEmpty_of_comp_sigmaOpenCover_eq A B φ

/-- A morphism of sheaves of modules on a coproduct of schemes is determined by its restrictions to
the summands. -/
public theorem injective_map_sigmaι (A B : (∐ Z).Modules) :
    Function.Injective (fun (ψ : A ⟶ B) k ↦
      (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.map ψ) :=
  injective_map_openCover (sigmaOpenCover Z) A B

/-- Restriction to the summands is a bijection from the morphisms `A ⟶ B` of sheaves of modules
on `∐ Z k` onto the families of morphisms of their restrictions, with no compatibility condition
on the family. -/
public theorem bijective_map_sigmaι (A B : (∐ Z).Modules) :
    Function.Bijective (fun (ψ : A ⟶ B) k ↦
      (modulePullbackPseudofunctor.map (Sigma.ι Z k).op.toLoc).toFunctor.map ψ) :=
  ⟨injective_map_sigmaι A B,
    fun φ ↦ (exists_hom_of_summandHoms A B φ).imp fun _ h ↦ funext h⟩

section QuasiInverse

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

section PullHom

variable {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

/-- Pulling back an identity gives an identity. -/
public theorem pullHom_one {X₁ : C} {M₁ : F.obj (.mk (op X₁))} {Y : C} {f₁ : Y ⟶ X₁}
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (h : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ h h = 𝟙 _ := by
  simp [pullHom]

/-- Pulling back a composition gives the composition of the pullbacks. -/
public theorem pullHom_comp {X₁ X₂ X₃ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {M₃ : F.obj (.mk (op X₃))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ h₁ h₃ =
      pullHom φ g gf₁ gf₂ h₁ h₂ ≫ pullHom ψ g gf₂ gf₃ h₂ h₃ := by
  simp [pullHom, ← reassoc_of% Cat.Hom₂.comp_app]

/-- The pullback of an isomorphism is an isomorphism. -/
public instance isIso_pullHom {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) : IsIso (pullHom φ g gf₁ gf₂ h₁ h₂) := by
  rw [pullHom]
  infer_instance

/-- The pullback of an inverse is the inverse of the pullback. -/
public theorem pullHom_inv {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (inv φ) g gf₂ gf₁ h₂ h₁ = inv (pullHom φ g gf₁ gf₂ h₁ h₂) := by
  have : IsIso (pullHom φ g gf₁ gf₂ h₁ h₂) := isIso_pullHom φ g gf₁ gf₂ h₁ h₂
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  rw [← pullHom_comp φ (inv φ) g gf₁ gf₂ gf₁ h₁ h₂ h₁, IsIso.hom_inv_id, pullHom_one]

end PullHom

/-- The pullback of a sheaf of modules along a morphism of schemes, in the spelling of
`AlgebraicGeometry.modulePullbackPseudofunctor`. -/
public noncomputable abbrev pullMod {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : modulePullbackPseudofunctor.obj (.mk (op Z))) :
    modulePullbackPseudofunctor.obj (.mk (op Y)) :=
  (modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.obj M

section Covers

/-- The index type of the summand covering of `∐ Z k` is `u`-small. -/
local instance smallSigmaOpenCoverIndex : Small.{u} (sigmaOpenCover Z).I₀ := ‹Small.{u} I›

/-- An open covering of a scheme has no overlaps when only a scheme with no points maps compatibly
to two distinct members. -/
public def NoOverlap {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y) : Prop :=
  ∀ k l, k ≠ l → ∀ {V : Scheme.{u}} (a : V ⟶ 𝒰.X k) (b : V ⟶ 𝒰.X l),
    a ≫ 𝒰.f k = b ≫ 𝒰.f l → IsEmpty V

/-- The summand covering of a coproduct of schemes has no overlaps. -/
public theorem noOverlap_sigmaOpenCover : NoOverlap (sigmaOpenCover Z) :=
  isEmpty_of_comp_sigmaOpenCover_eq

/-- The one-member open covering of a scheme by itself. -/
public noncomputable def selfCover (Y : Scheme.{u}) : Scheme.OpenCover.{w} Y :=
  Scheme.Cover.mkOfCovers PUnit.{w + 1} (fun _ ↦ Y) (fun _ ↦ 𝟙 Y) fun x ↦ ⟨⟨⟩, x, by simp⟩

/-- The one-member covering has no overlaps, there being no two distinct members. -/
public theorem noOverlap_selfCover (Y : Scheme.{u}) : NoOverlap (selfCover.{w} Y) :=
  fun k l hkl ↦ absurd (Subsingleton.elim (α := PUnit.{w + 1}) k l) hkl

/-- The refinement of an open covering making a given morphism factor through the members of a
covering of its target: its members are the fibre products `𝒰.X k ×_{Z'} 𝒲.X m`, indexed by pairs.
-/
public noncomputable def refineCover {Y Z' : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (𝒲 : Scheme.OpenCover.{w} Z') (u : Y ⟶ Z') : Scheme.OpenCover.{w} Y :=
  Scheme.Cover.mkOfCovers (𝒰.I₀ × 𝒲.I₀) (fun k ↦ pullback (𝒰.f k.1 ≫ u) (𝒲.f k.2))
    (fun k ↦ pullback.fst _ _ ≫ 𝒰.f k.1)
    (fun x ↦ by
      obtain ⟨k, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨m, z, hz⟩ := 𝒲.exists_eq ((𝒰.f k ≫ u) y)
      obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := 𝒰.f k ≫ u) (g := 𝒲.f m) y z hz.symm
      exact ⟨(k, m), p, by rw [Scheme.Hom.comp_apply, hp₁]⟩)
    (fun _ ↦ inferInstance)

variable {Y Z' : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y) (𝒲 : Scheme.OpenCover.{w} Z')
  (u : Y ⟶ Z')

/-- The projection of a member of `AlgebraicGeometry.refineCover` to a member of `𝒰`. -/
public noncomputable def refineCoverFst (k : 𝒰.I₀ × 𝒲.I₀) :
    (refineCover 𝒰 𝒲 u).X k ⟶ 𝒰.X k.1 :=
  pullback.fst _ _

/-- The projection of a member of `AlgebraicGeometry.refineCover` to a member of `𝒲`. -/
public noncomputable def refineCoverSnd (k : 𝒰.I₀ × 𝒲.I₀) :
    (refineCover 𝒰 𝒲 u).X k ⟶ 𝒲.X k.2 :=
  pullback.snd _ _

/-- A member of `AlgebraicGeometry.refineCover` lies over the corresponding member of `𝒰`. -/
@[reassoc (attr := simp)]
public theorem refineCoverFst_f (k : 𝒰.I₀ × 𝒲.I₀) :
    refineCoverFst 𝒰 𝒲 u k ≫ 𝒰.f k.1 = (refineCover 𝒰 𝒲 u).f k := rfl

/-- On a member of `AlgebraicGeometry.refineCover` the given morphism factors through the
corresponding member of `𝒲`. -/
@[reassoc (attr := simp)]
public theorem refineCover_f_comp (k : 𝒰.I₀ × 𝒲.I₀) :
    (refineCover 𝒰 𝒲 u).f k ≫ u = refineCoverSnd 𝒰 𝒲 u k ≫ 𝒲.f k.2 :=
  (Category.assoc _ _ _).trans pullback.condition

/-- The refinement of two overlap-free coverings is overlap-free. -/
public theorem noOverlap_refineCover (h𝒰 : NoOverlap 𝒰) (h𝒲 : NoOverlap 𝒲) :
    NoOverlap (refineCover 𝒰 𝒲 u) := by
  rintro ⟨k₁, k₂⟩ ⟨l₁, l₂⟩ hkl V a b hab
  by_cases hk : k₁ = l₁
  · subst hk
    refine h𝒲 k₂ l₂ (fun h ↦ hkl (by rw [h])) (a ≫ refineCoverSnd 𝒰 𝒲 u (k₁, k₂))
      (b ≫ refineCoverSnd 𝒰 𝒲 u (k₁, l₂)) ?_
    rw [Category.assoc, Category.assoc, ← refineCover_f_comp, ← refineCover_f_comp,
      ← Category.assoc, ← Category.assoc, hab]
  · refine h𝒰 k₁ l₁ hk (a ≫ refineCoverFst 𝒰 𝒲 u (k₁, k₂))
      (b ≫ refineCoverFst 𝒰 𝒲 u (l₁, l₂)) ?_
    rw [Category.assoc, Category.assoc, refineCoverFst_f, refineCoverFst_f, hab]

end Covers

section Gluing

variable {V : Scheme.{u}} {Z₁ Z₂ : Scheme.{u}}
  {M₁ : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
  {M₂ : modulePullbackPseudofunctor.obj (.mk (op Z₂))}

/-- The comparison isomorphism of the pullback pseudofunctor at a factorization `g ≫ p = gp`: the
pullback along `gp` of a sheaf of modules is the pullback along `g` of its pullback along `p`. -/
public noncomputable def pullModComp {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (p : Y ⟶ Z₁)
    (gp : Y' ⟶ Z₁) (h : g ≫ p = gp) (M : modulePullbackPseudofunctor.obj (.mk (op Z₁))) :
    pullMod gp M ≅ pullMod g (pullMod p M) :=
  (Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' p.op.toLoc g.op.toLoc gp.op.toLoc
    (by rw [← h]; cat_disch))).app M

/-- The comparison isomorphism of the pullback pseudofunctor at the identity: the pullback of a
sheaf of modules along an identity is the sheaf itself. -/
public noncomputable def pullModId (Y : Scheme.{u})
    (M : modulePullbackPseudofunctor.obj (.mk (op Y))) : pullMod (𝟙 Y) M ≅ M :=
  (Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapId (.mk (op Y)))).app M

/-- Two morphisms between pullbacks of sheaves of modules on a scheme with no points agree. -/
public theorem hom_eq_of_isEmpty {g₁ : V ⟶ Z₁} {g₂ : V ⟶ Z₂} [IsEmpty V]
    (ψ ψ' : pullMod g₁ M₁ ⟶ pullMod g₂ M₂) : ψ = ψ' :=
  @Subsingleton.elim _ (subsingleton_hom_pseudofunctor _ _) _ _

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` is conjugation of the pullback of
a morphism by the comparison isomorphisms. -/
public theorem pullHom_eq_conj {Y : Scheme.{u}} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    (φ : pullMod f₁ M₁ ⟶ pullMod f₂ M₂) {Y' : Scheme.{u}} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁)
    (gf₂ : Y' ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ = (pullModComp g f₁ gf₁ h₁ M₁).hom ≫
      (modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.map φ ≫
        (pullModComp g f₂ gf₂ h₂ M₂).inv := rfl

/-- `AlgebraicGeometry.injective_map_openCover` at the pullback pseudofunctor's spelling of the
category of sheaves of modules. -/
public theorem injective_map_openCover' {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (A B : modulePullbackPseudofunctor.obj (.mk (op Y))) :
    Function.Injective (fun (ψ : A ⟶ B) k ↦
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.map ψ) :=
  injective_map_openCover 𝒰 A B

/-- `AlgebraicGeometry.exists_hom_of_disjointCoverHoms` at the pullback pseudofunctor's spelling of
the category of sheaves of modules. -/
public theorem exists_hom_of_disjointCoverHoms' {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} Y)
    (hdisj : NoOverlap 𝒰) (A B : modulePullbackPseudofunctor.obj (.mk (op Y)))
    (φ : ∀ k, pullMod (𝒰.f k) A ⟶ pullMod (𝒰.f k) B) :
    ∃ ψ : A ⟶ B, ∀ k,
      (modulePullbackPseudofunctor.map (𝒰.f k).op.toLoc).toFunctor.map ψ = φ k :=
  exists_hom_of_disjointCoverHoms 𝒰 hdisj A B φ

/-- A morphism between pullbacks of sheaves of modules is determined by its restrictions to the
members of an open covering. -/
public theorem pullHom_ext (𝒱 : Scheme.OpenCover.{w} V) {g₁ : V ⟶ Z₁} {g₂ : V ⟶ Z₂}
    (gf₁ : ∀ k, 𝒱.X k ⟶ Z₁) (gf₂ : ∀ k, 𝒱.X k ⟶ Z₂) (h₁ : ∀ k, 𝒱.f k ≫ g₁ = gf₁ k)
    (h₂ : ∀ k, 𝒱.f k ≫ g₂ = gf₂ k) {ψ ψ' : pullMod g₁ M₁ ⟶ pullMod g₂ M₂}
    (h : ∀ k, pullHom ψ (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k) =
      pullHom ψ' (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k)) : ψ = ψ' := by
  refine injective_map_openCover' 𝒱 _ _ (funext fun k ↦ ?_)
  dsimp only
  rw [map_eq_pullHom ψ (𝒱.f k) _ _ (h₁ k) (h₂ k),
    map_eq_pullHom ψ' (𝒱.f k) _ _ (h₁ k) (h₂ k), h k]

/-- A morphism between pullbacks of sheaves of modules can be glued from an arbitrary family of
restrictions to the members of an overlap-free open covering. -/
public theorem exists_pullHom (𝒱 : Scheme.OpenCover.{w} V) (h𝒱 : NoOverlap 𝒱)
    (g₁ : V ⟶ Z₁) (g₂ : V ⟶ Z₂) (gf₁ : ∀ k, 𝒱.X k ⟶ Z₁) (gf₂ : ∀ k, 𝒱.X k ⟶ Z₂)
    (h₁ : ∀ k, 𝒱.f k ≫ g₁ = gf₁ k) (h₂ : ∀ k, 𝒱.f k ≫ g₂ = gf₂ k)
    (φ : ∀ k, pullMod (gf₁ k) M₁ ⟶ pullMod (gf₂ k) M₂) :
    ∃ ψ : pullMod g₁ M₁ ⟶ pullMod g₂ M₂, ∀ k,
      pullHom ψ (𝒱.f k) (gf₁ k) (gf₂ k) (h₁ k) (h₂ k) = φ k := by
  obtain ⟨ψ, hψ⟩ := exists_hom_of_disjointCoverHoms' 𝒱 h𝒱 (pullMod g₁ M₁) (pullMod g₂ M₂)
    (fun k ↦ (pullModComp (𝒱.f k) g₁ _ (h₁ k) M₁).inv ≫ φ k ≫
      (pullModComp (𝒱.f k) g₂ _ (h₂ k) M₂).hom)
  refine ⟨ψ, fun k ↦ ?_⟩
  rw [pullHom_eq_conj, hψ k, Category.assoc, Iso.hom_inv_id_assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The pullback of a morphism depends only on the morphism it is pulled back along, the
factorizations being propositions. -/
public theorem pullHom_congr_mor {Y : Scheme.{u}} {f₁ : V ⟶ Z₁} {f₂ : V ⟶ Z₂}
    (φ : pullMod f₁ M₁ ⟶ pullMod f₂ M₂) {g g' : Y ⟶ V} (hg : g = g') (gf₁ : Y ⟶ Z₁)
    (gf₂ : Y ⟶ Z₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₁' : g' ≫ f₁ = gf₁)
    (h₂' : g' ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ h₁ h₂ = pullHom φ g' gf₁ gf₂ h₁' h₂' := by
  subst hg; rfl

/-- `AlgebraicGeometry.pullHom_ext` with the factorizations through the members of the covering
taken to be the composites. -/
private theorem pullHom_ext_comp (𝒱 : Scheme.OpenCover.{w} V) {g₁ : V ⟶ Z₁} {g₂ : V ⟶ Z₂}
    {ψ ψ' : pullMod g₁ M₁ ⟶ pullMod g₂ M₂}
    (h : ∀ k, pullHom ψ (𝒱.f k) (𝒱.f k ≫ g₁) (𝒱.f k ≫ g₂) rfl rfl =
      pullHom ψ' (𝒱.f k) (𝒱.f k ≫ g₁) (𝒱.f k ≫ g₂) rfl rfl) : ψ = ψ' :=
  pullHom_ext 𝒱 _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) h

end Gluing

section Summands

/-- A morphism into a summand which lies over a morphism to the coproduct lies, after composition
with the structure morphism of the family, over the corresponding morphism to the base. -/
public theorem comp_f_eq_of_comp_sigmaι {V V' : Scheme.{u}} {q : V ⟶ T} {u : V ⟶ ∐ X}
    (hu : u ≫ Sigma.desc f = q) {h : V' ⟶ V} {i : I} {a : V' ⟶ X i}
    (ha : a ≫ Sigma.ι X i = h ≫ u) : a ≫ f i = h ≫ q := by
  rw [comp_desc_of_comp_sigmaι ha, Category.assoc, hu]

variable (D : QuasicoherentDescentData f)
  (N : modulePullbackPseudofunctor.obj (.mk (op (∐ X))))
  (κ : ∀ i, pullMod (Sigma.ι X i) N ≅ D.component i)

/-- The comparison at a summand, read as an isomorphism onto a pullback along an identity. -/
public noncomputable def summandBaseIso (i : I) :
    pullMod (Sigma.ι X i) N ≅ pullMod (𝟙 (X i)) (D.component i) :=
  κ i ≪≫ (pullModId (X i) (D.component i)).symm

/-- The comparison at a morphism into a summand: for `a : V ⟶ X i` lying over `u : V ⟶ ∐ X`, the
pullback of `N` along `u` is the pullback along `a` of the `i`-th component of `D`. -/
public noncomputable def summandCompAt {V : Scheme.{u}} {i : I} (a : V ⟶ X i) (u : V ⟶ ∐ X)
    (hu : a ≫ Sigma.ι X i = u) : pullMod u N ≅ pullMod a (D.component i) where
  hom := pullHom (summandBaseIso D N κ i).hom a u a hu (Category.comp_id a)
  inv := pullHom (summandBaseIso D N κ i).inv a a u (Category.comp_id a) hu
  hom_inv_id := by
    rw [← pullHom_comp (summandBaseIso D N κ i).hom (summandBaseIso D N κ i).inv a u a u hu
      (Category.comp_id a) hu, Iso.hom_inv_id, pullHom_one]
  inv_hom_id := by
    rw [← pullHom_comp (summandBaseIso D N κ i).inv (summandBaseIso D N κ i).hom a a u a
      (Category.comp_id a) hu (Category.comp_id a), Iso.inv_hom_id, pullHom_one]

/-- The comparison at a morphism into a summand is compatible with further pullback. -/
public theorem pullHom_summandCompAt_hom {V V' : Scheme.{u}} {i : I} (a : V ⟶ X i)
    (u : V ⟶ ∐ X) (hu : a ≫ Sigma.ι X i = u) (h : V' ⟶ V) (u' : V' ⟶ ∐ X) (hu' : h ≫ u = u') :
    pullHom (summandCompAt D N κ a u hu).hom h u' (h ≫ a) hu' rfl =
      (summandCompAt D N κ (h ≫ a) u' (by rw [Category.assoc, hu, hu'])).hom :=
  pullHom_pullHom _ a u a h u' (h ≫ a) hu (Category.comp_id a) hu' rfl

/-- The inverse comparison at a morphism into a summand is compatible with further pullback. -/
public theorem pullHom_summandCompAt_inv {V V' : Scheme.{u}} {i : I} (a : V ⟶ X i)
    (u : V ⟶ ∐ X) (hu : a ≫ Sigma.ι X i = u) (h : V' ⟶ V) (u' : V' ⟶ ∐ X) (hu' : h ≫ u = u') :
    pullHom (summandCompAt D N κ a u hu).inv h (h ≫ a) u' rfl hu' =
      (summandCompAt D N κ (h ≫ a) u' (by rw [Category.assoc, hu, hu'])).inv :=
  pullHom_pullHom _ a a u h (h ≫ a) u' (Category.comp_id a) hu rfl hu'

/-- The transition of the coproduct datum at a pair of morphisms factoring through summands: the
transition of `D` between the two components, conjugated by the comparisons. -/
public noncomputable def summandTransition {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    {i j : I} (a : V ⟶ X i) (b : V ⟶ X j) (hu : a ≫ Sigma.ι X i = u)
    (hv : b ≫ Sigma.ι X j = v) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    pullMod u N ⟶ pullMod v N :=
  (summandCompAt D N κ a u hu).hom ≫ D.obj.hom q a b ha hb ≫ (summandCompAt D N κ b v hv).inv

/-- `AlgebraicGeometry.summandTransition` does not depend on the factorizations through summands,
nor on the morphism to the base they lie over. -/
public theorem summandTransition_congr {V : Scheme.{u}} {q q' : V ⟶ T} {u v : V ⟶ ∐ X}
    {i j i' j' : I} (a : V ⟶ X i) (b : V ⟶ X j) (a' : V ⟶ X i')
    (b' : V ⟶ X j') (hu : a ≫ Sigma.ι X i = u) (hv : b ≫ Sigma.ι X j = v)
    (hu' : a' ≫ Sigma.ι X i' = u) (hv' : b' ≫ Sigma.ι X j' = v) (ha : a ≫ f i = q)
    (hb : b ≫ f j = q) (ha' : a' ≫ f i' = q') (hb' : b' ≫ f j' = q') :
    summandTransition D N κ q u v a b hu hv ha hb =
      summandTransition D N κ q' u v a' b' hu' hv' ha' hb' := by
  rcases eq_or_ne i i' with rfl | hne
  · obtain rfl : a = a' := (cancel_mono (Sigma.ι X i)).mp (hu.trans hu'.symm)
    obtain rfl : q = q' := ha.symm.trans ha'
    rcases eq_or_ne j j' with rfl | hne
    · obtain rfl : b = b' := (cancel_mono (Sigma.ι X j)).mp (hv.trans hv'.symm)
      rfl
    · have : IsEmpty V := isEmpty_of_commSq_sigmaι_of_ne ⟨hv.trans hv'.symm⟩ hne
      exact hom_eq_of_isEmpty _ _
  · have : IsEmpty V := isEmpty_of_commSq_sigmaι_of_ne ⟨hu.trans hu'.symm⟩ hne
    exact hom_eq_of_isEmpty _ _

/-- `AlgebraicGeometry.summandTransition` is compatible with pullback. -/
public theorem pullHom_summandTransition {V V' : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    {i j : I} (a : V ⟶ X i) (b : V ⟶ X j) (hu : a ≫ Sigma.ι X i = u)
    (hv : b ≫ Sigma.ι X j = v) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (h : V' ⟶ V)
    (u' v' : V' ⟶ ∐ X) (hu' : h ≫ u = u') (hv' : h ≫ v = v') :
    pullHom (summandTransition D N κ q u v a b hu hv ha hb) h u' v' hu' hv' =
      summandTransition D N κ (h ≫ q) u' v' (h ≫ a) (h ≫ b)
        (by rw [Category.assoc, hu, hu']) (by rw [Category.assoc, hv, hv'])
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  simp only [summandTransition]
  rw [pullHom_comp _ _ h u' (h ≫ a) v' hu' rfl hv',
    pullHom_comp _ _ h (h ≫ a) (h ≫ b) v' rfl rfl hv', pullHom_summandCompAt_hom,
    D.obj.pullHom_hom h q (h ≫ q) rfl a b ha hb (h ≫ a) (h ≫ b) rfl rfl,
    pullHom_summandCompAt_inv]

/-- `AlgebraicGeometry.summandTransition` at a repeated morphism is the identity. -/
public theorem summandTransition_self {V : Scheme.{u}} (q : V ⟶ T) (u : V ⟶ ∐ X) {i : I}
    (a : V ⟶ X i) (hu : a ≫ Sigma.ι X i = u) (ha : a ≫ f i = q) :
    summandTransition D N κ q u u a a hu hu ha ha = 𝟙 _ := by
  simp only [summandTransition, D.obj.hom_self q a ha, Category.id_comp, Iso.hom_inv_id]

/-- The transitions `AlgebraicGeometry.summandTransition` compose. -/
public theorem summandTransition_comp {V : Scheme.{u}} (q : V ⟶ T) (u v u₃ : V ⟶ ∐ X)
    {i j k : I} (a : V ⟶ X i) (b : V ⟶ X j) (c : V ⟶ X k) (hu : a ≫ Sigma.ι X i = u)
    (hv : b ≫ Sigma.ι X j = v) (hw : c ≫ Sigma.ι X k = u₃) (ha : a ≫ f i = q)
    (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    summandTransition D N κ q u v a b hu hv ha hb ≫
        summandTransition D N κ q v u₃ b c hv hw hb hc =
      summandTransition D N κ q u u₃ a c hu hw ha hc := by
  simp only [summandTransition, Category.assoc, Iso.inv_hom_id_assoc]
  rw [D.obj.hom_comp_assoc q a b c ha hb hc]

/-- An overlap-free covering can be refined, overlap-free, so that one further morphism to a
coproduct of schemes factors through summands on each member. -/
public theorem exists_splitStep {V : Scheme.{u}} (𝒰 : Scheme.OpenCover.{w} V)
    (h𝒰 : NoOverlap 𝒰) (u : V ⟶ ∐ X) :
    ∃ (𝒰' : Scheme.OpenCover.{w} V) (_ : NoOverlap 𝒰') (ρ : 𝒰'.I₀ → 𝒰.I₀)
      (θ : ∀ k, 𝒰'.X k ⟶ 𝒰.X (ρ k)) (iu : 𝒰'.I₀ → I) (A : ∀ k, 𝒰'.X k ⟶ X (iu k)),
      (∀ k, θ k ≫ 𝒰.f (ρ k) = 𝒰'.f k) ∧
        (∀ k, 𝒰'.f k ≫ u = A k ≫ Sigma.ι X (iu k)) :=
  ⟨refineCover 𝒰 (sigmaOpenCover X) u,
    noOverlap_refineCover _ _ _ h𝒰 noOverlap_sigmaOpenCover, fun k ↦ k.1,
    fun k ↦ refineCoverFst 𝒰 (sigmaOpenCover X) u k, fun k ↦ k.2,
    fun k ↦ refineCoverSnd 𝒰 (sigmaOpenCover X) u k,
    fun k ↦ refineCoverFst_f 𝒰 (sigmaOpenCover X) u k,
    fun k ↦ refineCover_f_comp 𝒰 (sigmaOpenCover X) u k⟩

/-- A scheme admits an overlap-free open covering on which two given morphisms to a coproduct of
schemes both factor through summands. -/
public theorem exists_splitCover₂ (V : Scheme.{u}) (u v : V ⟶ ∐ X) :
    ∃ (𝒞 : Scheme.OpenCover.{w} V) (_ : NoOverlap 𝒞) (ia ib : 𝒞.I₀ → I)
      (A : ∀ k, 𝒞.X k ⟶ X (ia k)) (B : ∀ k, 𝒞.X k ⟶ X (ib k)),
      (∀ k, 𝒞.f k ≫ u = A k ≫ Sigma.ι X (ia k)) ∧
        (∀ k, 𝒞.f k ≫ v = B k ≫ Sigma.ι X (ib k)) := by
  obtain ⟨𝒰, h𝒰, -, -, iu, A, -, hA⟩ :=
    exists_splitStep (selfCover.{w} V) (noOverlap_selfCover V) u
  obtain ⟨𝒰', h𝒰', ρ, θ, iv, B, hθ, hB⟩ := exists_splitStep 𝒰 h𝒰 v
  refine ⟨𝒰', h𝒰', fun k ↦ iu (ρ k), iv, fun k ↦ θ k ≫ A (ρ k), B, fun k ↦ ?_, hB⟩
  rw [← hθ k, Category.assoc, hA (ρ k), Category.assoc]

/-- Any morphism factors, locally on a refinement of its source, through the members of a given
open covering of its target. -/
public theorem exists_factorCover {V V' : Scheme.{u}} (𝒞 : Scheme.OpenCover.{w} V)
    (h : V' ⟶ V) : ∃ (𝒟 : Scheme.OpenCover.{w} V') (μ : 𝒟.I₀ → 𝒞.I₀)
      (C : ∀ m, 𝒟.X m ⟶ 𝒞.X (μ m)), ∀ m, 𝒟.f m ≫ h = C m ≫ 𝒞.f (μ m) :=
  ⟨refineCover (selfCover V') 𝒞 h, fun m ↦ m.2, fun m ↦ refineCoverSnd _ _ _ m,
    fun m ↦ refineCover_f_comp _ _ _ m⟩

/-- A morphism of pullbacks of `N` that restricts to the transitions of `D` on the members of a
covering on which `u` and `v` factor through summands restricts to them along every morphism along
which `u` and `v` factor through summands. -/
public theorem pullHom_eq_summandTransition {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) (𝒞 : Scheme.OpenCover.{w} V)
    (ia ib : 𝒞.I₀ → I) (A : ∀ k, 𝒞.X k ⟶ X (ia k)) (B : ∀ k, 𝒞.X k ⟶ X (ib k))
    (hA : ∀ k, 𝒞.f k ≫ u = A k ≫ Sigma.ι X (ia k))
    (hB : ∀ k, 𝒞.f k ≫ v = B k ≫ Sigma.ι X (ib k)) (ψ : pullMod u N ⟶ pullMod v N)
    (hψ : ∀ k, pullHom ψ (𝒞.f k) (𝒞.f k ≫ u) (𝒞.f k ≫ v) rfl rfl =
      summandTransition D N κ (𝒞.f k ≫ q) (𝒞.f k ≫ u) (𝒞.f k ≫ v) (A k) (B k)
        (hA k).symm (hB k).symm (comp_f_eq_of_comp_sigmaι hu (hA k).symm)
        (comp_f_eq_of_comp_sigmaι hv (hB k).symm))
    {V' : Scheme.{u}} (h : V' ⟶ V) {i j : I} (a : V' ⟶ X i) (b : V' ⟶ X j)
    (ha : a ≫ Sigma.ι X i = h ≫ u) (hb : b ≫ Sigma.ι X j = h ≫ v) :
    pullHom ψ h (h ≫ u) (h ≫ v) rfl rfl =
      summandTransition D N κ (h ≫ q) (h ≫ u) (h ≫ v) a b ha hb
        (comp_f_eq_of_comp_sigmaι hu ha) (comp_f_eq_of_comp_sigmaι hv hb) := by
  obtain ⟨𝒟, μ, C, hC⟩ := exists_factorCover 𝒞 h
  refine pullHom_ext_comp 𝒟 fun m ↦ ?_
  have hw (w : V ⟶ ∐ X) : C m ≫ 𝒞.f (μ m) ≫ w = 𝒟.f m ≫ h ≫ w := by
    rw [← Category.assoc (C m), ← hC m, Category.assoc]
  rw [pullHom_summandTransition D N κ (h ≫ q) (h ≫ u) (h ≫ v) a b ha hb
      (comp_f_eq_of_comp_sigmaι hu ha) (comp_f_eq_of_comp_sigmaι hv hb) (𝒟.f m)
      (𝒟.f m ≫ h ≫ u) (𝒟.f m ≫ h ≫ v) rfl rfl,
    pullHom_pullHom ψ h (h ≫ u) (h ≫ v) (𝒟.f m) (𝒟.f m ≫ h ≫ u) (𝒟.f m ≫ h ≫ v) rfl rfl
      rfl rfl,
    pullHom_congr_mor ψ (hC m) (𝒟.f m ≫ h ≫ u) (𝒟.f m ≫ h ≫ v) _ _
      ((Category.assoc ..).trans (hw u)) ((Category.assoc ..).trans (hw v)),
    ← pullHom_pullHom ψ (𝒞.f (μ m)) (𝒞.f (μ m) ≫ u) (𝒞.f (μ m) ≫ v) (C m) (𝒟.f m ≫ h ≫ u)
      (𝒟.f m ≫ h ≫ v) rfl rfl (hw u) (hw v),
    hψ (μ m),
    pullHom_summandTransition D N κ (𝒞.f (μ m) ≫ q) (𝒞.f (μ m) ≫ u) (𝒞.f (μ m) ≫ v)
      (A (μ m)) (B (μ m)) (hA (μ m)).symm (hB (μ m)).symm
      (comp_f_eq_of_comp_sigmaι hu (hA (μ m)).symm)
      (comp_f_eq_of_comp_sigmaι hv (hB (μ m)).symm) (C m) (𝒟.f m ≫ h ≫ u) (𝒟.f m ≫ h ≫ v)
      (hw u) (hw v)]
  apply summandTransition_congr

/-- For two morphisms `u v : V ⟶ ∐ X` lying over a common `q : V ⟶ T` there is a morphism
`u^* N ⟶ v^* N` whose restriction along *any* morphism `h : V' ⟶ V` along which `u` and `v` factor
through summands is the corresponding transition of `D`. -/
public theorem exists_sigmaTransition {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) :
    ∃ ψ : pullMod u N ⟶ pullMod v N, ∀ {V' : Scheme.{u}} (h : V' ⟶ V) {i j : I}
      (a : V' ⟶ X i) (b : V' ⟶ X j) (ha : a ≫ Sigma.ι X i = h ≫ u)
      (hb : b ≫ Sigma.ι X j = h ≫ v),
      pullHom ψ h (h ≫ u) (h ≫ v) rfl rfl =
        summandTransition D N κ (h ≫ q) (h ≫ u) (h ≫ v) a b ha hb
          (comp_f_eq_of_comp_sigmaι hu ha) (comp_f_eq_of_comp_sigmaι hv hb) := by
  obtain ⟨𝒞, h𝒞, ia, ib, A, B, hA, hB⟩ := exists_splitCover₂ (X := X) V u v
  obtain ⟨ψ, hψ⟩ := exists_pullHom 𝒞 h𝒞 u v (fun k ↦ 𝒞.f k ≫ u) (fun k ↦ 𝒞.f k ≫ v)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun k ↦ summandTransition D N κ (𝒞.f k ≫ q) (𝒞.f k ≫ u)
      (𝒞.f k ≫ v) (A k) (B k) (hA k).symm (hB k).symm
      (comp_f_eq_of_comp_sigmaι hu (hA k).symm) (comp_f_eq_of_comp_sigmaι hv (hB k).symm))
  exact ⟨ψ, fun {_} h {_ _} a b ha hb ↦
    pullHom_eq_summandTransition D N κ q u v hu hv 𝒞 ia ib A B hA hB ψ hψ h a b ha hb⟩

/-- A scheme admits an open covering on which one given morphism to a coproduct of schemes factors
through summands. -/
public theorem exists_splitCover₁ (V : Scheme.{u}) (u : V ⟶ ∐ X) :
    ∃ (𝒞 : Scheme.OpenCover.{w} V) (ia : 𝒞.I₀ → I) (A : ∀ k, 𝒞.X k ⟶ X (ia k)),
      ∀ k, 𝒞.f k ≫ u = A k ≫ Sigma.ι X (ia k) := by
  obtain ⟨𝒰, -, -, -, iu, A, -, hA⟩ :=
    exists_splitStep (selfCover.{w} V) (noOverlap_selfCover V) u
  exact ⟨𝒰, iu, A, hA⟩

/-- A scheme admits an open covering on which three given morphisms to a coproduct of schemes all
factor through summands. -/
public theorem exists_splitCover₃ (V : Scheme.{u}) (u v u₃ : V ⟶ ∐ X) :
    ∃ (𝒞 : Scheme.OpenCover.{w} V) (ia ib ic : 𝒞.I₀ → I) (A : ∀ k, 𝒞.X k ⟶ X (ia k))
      (B : ∀ k, 𝒞.X k ⟶ X (ib k)) (Cc : ∀ k, 𝒞.X k ⟶ X (ic k)),
      (∀ k, 𝒞.f k ≫ u = A k ≫ Sigma.ι X (ia k)) ∧
        (∀ k, 𝒞.f k ≫ v = B k ≫ Sigma.ι X (ib k)) ∧
          ∀ k, 𝒞.f k ≫ u₃ = Cc k ≫ Sigma.ι X (ic k) := by
  obtain ⟨𝒞, h𝒞, ia, ib, A, B, hA, hB⟩ := exists_splitCover₂ (X := X) V u v
  obtain ⟨𝒞', -, ρ, θ, ic, Cc, hθ, hC⟩ := exists_splitStep 𝒞 h𝒞 u₃
  refine ⟨𝒞', fun k ↦ ia (ρ k), fun k ↦ ib (ρ k), ic, fun k ↦ θ k ≫ A (ρ k),
    fun k ↦ θ k ≫ B (ρ k), Cc, fun k ↦ ?_, fun k ↦ ?_, hC⟩
  · rw [← hθ k, Category.assoc, hA (ρ k), Category.assoc]
  · rw [← hθ k, Category.assoc, hB (ρ k), Category.assoc]

/-- The transition of the coproduct datum: a morphism `u^* N ⟶ v^* N` restricting to the
transitions of `D` along every morphism along which `u` and `v` factor through summands. -/
public noncomputable def sigmaTransition {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) : pullMod u N ⟶ pullMod v N :=
  (exists_sigmaTransition D N κ q u v hu hv).choose

/-- The defining property of the transition of the coproduct datum: along any morphism along which
`u` and `v` factor through summands it restricts to the corresponding transition of `D`. -/
public theorem pullHom_sigmaTransition {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) {V' : Scheme.{u}} (h : V' ⟶ V)
    (u' v' : V' ⟶ ∐ X) (hu' : h ≫ u = u') (hv' : h ≫ v = v') {i j : I} (a : V' ⟶ X i)
    (b : V' ⟶ X j) (ha : a ≫ Sigma.ι X i = u') (hb : b ≫ Sigma.ι X j = v') :
    pullHom (sigmaTransition D N κ q u v hu hv) h u' v' hu' hv' =
      summandTransition D N κ (h ≫ q) u' v' a b ha hb
        (comp_f_eq_of_comp_sigmaι hu (ha.trans hu'.symm))
        (comp_f_eq_of_comp_sigmaι hv (hb.trans hv'.symm)) := by
  subst hu'
  subst hv'
  exact (exists_sigmaTransition D N κ q u v hu hv).choose_spec h a b ha hb

/-- `AlgebraicGeometry.pullHom_sigmaTransition` along the members of a covering on which `u` and
`v` factor through summands. -/
private theorem pullHom_sigmaTransition_cover {V : Scheme.{u}} (q : V ⟶ T) (u v : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) (𝒞 : Scheme.OpenCover.{w} V)
    {ia ib : 𝒞.I₀ → I} {A : ∀ k, 𝒞.X k ⟶ X (ia k)} {B : ∀ k, 𝒞.X k ⟶ X (ib k)}
    (hA : ∀ k, 𝒞.f k ≫ u = A k ≫ Sigma.ι X (ia k))
    (hB : ∀ k, 𝒞.f k ≫ v = B k ≫ Sigma.ι X (ib k)) (k : 𝒞.I₀) :
    pullHom (sigmaTransition D N κ q u v hu hv) (𝒞.f k) (𝒞.f k ≫ u) (𝒞.f k ≫ v) rfl rfl =
      summandTransition D N κ (𝒞.f k ≫ q) (𝒞.f k ≫ u) (𝒞.f k ≫ v) (A k) (B k)
        (hA k).symm (hB k).symm (comp_f_eq_of_comp_sigmaι hu (hA k).symm)
        (comp_f_eq_of_comp_sigmaι hv (hB k).symm) :=
  pullHom_sigmaTransition D N κ q u v hu hv (𝒞.f k) _ _ rfl rfl (A k) (B k) (hA k).symm
    (hB k).symm

/-- The transition of the coproduct datum at a repeated morphism is the identity. -/
public theorem sigmaTransition_self {V : Scheme.{u}} (q : V ⟶ T) (u : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) : sigmaTransition D N κ q u u hu hu = 𝟙 _ := by
  obtain ⟨𝒞, ia, A, hA⟩ := exists_splitCover₁ (X := X) V u
  refine pullHom_ext_comp 𝒞 fun k ↦ ?_
  rw [pullHom_sigmaTransition_cover D N κ q u u hu hu 𝒞 hA hA k, summandTransition_self,
    pullHom_one]

/-- The transitions of the coproduct datum compose. -/
public theorem sigmaTransition_comp {V : Scheme.{u}} (q : V ⟶ T) (u v u₃ : V ⟶ ∐ X)
    (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) (hw : u₃ ≫ Sigma.desc f = q) :
    sigmaTransition D N κ q u v hu hv ≫ sigmaTransition D N κ q v u₃ hv hw =
      sigmaTransition D N κ q u u₃ hu hw := by
  obtain ⟨𝒞, ia, ib, ic, A, B, Cc, hA, hB, hC⟩ := exists_splitCover₃ (X := X) V u v u₃
  refine pullHom_ext_comp 𝒞 fun k ↦ ?_
  rw [pullHom_comp _ _ (𝒞.f k) (𝒞.f k ≫ u) (𝒞.f k ≫ v) (𝒞.f k ≫ u₃) rfl rfl rfl,
    pullHom_sigmaTransition_cover D N κ q u v hu hv 𝒞 hA hB k,
    pullHom_sigmaTransition_cover D N κ q v u₃ hv hw 𝒞 hB hC k,
    pullHom_sigmaTransition_cover D N κ q u u₃ hu hw 𝒞 hA hC k, summandTransition_comp]

/-- The transition of the coproduct datum is compatible with pullback. -/
public theorem pullHom_sigmaTransition_eq {V V' : Scheme.{u}} (g : V' ⟶ V) (q : V ⟶ T)
    (q' : V' ⟶ T) (hq : g ≫ q = q') (u v : V ⟶ ∐ X) (hu : u ≫ Sigma.desc f = q)
    (hv : v ≫ Sigma.desc f = q) (gu gv : V' ⟶ ∐ X) (hgu : g ≫ u = gu) (hgv : g ≫ v = gv) :
    pullHom (sigmaTransition D N κ q u v hu hv) g gu gv hgu hgv =
      sigmaTransition D N κ q' gu gv (by rw [← hgu, Category.assoc, hu, hq])
        (by rw [← hgv, Category.assoc, hv, hq]) := by
  obtain ⟨𝒞, -, ia, ib, A, B, hA, hB⟩ := exists_splitCover₂ (X := X) V' gu gv
  refine pullHom_ext_comp 𝒞 fun k ↦ ?_
  rw [pullHom_pullHom (sigmaTransition D N κ q u v hu hv) g gu gv (𝒞.f k) (𝒞.f k ≫ gu)
      (𝒞.f k ≫ gv) hgu hgv rfl rfl,
    pullHom_sigmaTransition D N κ q u v hu hv (𝒞.f k ≫ g) (𝒞.f k ≫ gu) (𝒞.f k ≫ gv)
      (by rw [Category.assoc, hgu]) (by rw [Category.assoc, hgv]) (A k) (B k)
      (hA k).symm (hB k).symm,
    pullHom_sigmaTransition_cover D N κ q' gu gv _ _ 𝒞 hA hB k]
  apply summandTransition_congr

/-- The quasi-coherent descent datum for the one-element family given by the coproduct, whose sole
component is `N` and whose transitions are the glued transitions of `D`. -/
public noncomputable def sigmaDescentData :
    modulePullbackPseudofunctor.DescentData (fun _ : PUnit.{1} ↦ Sigma.desc f) where
  obj _ := N
  hom _ q _ _ u v hu hv := sigmaTransition D N κ q u v hu hv
  pullHom_hom _ _ g q q' hq _ _ u v hu hv gu gv hgu hgv :=
    pullHom_sigmaTransition_eq D N κ g q q' hq u v hu hv gu gv hgu hgv
  hom_self _ q _ u hu := sigmaTransition_self D N κ q u hu
  hom_comp _ q _ _ _ u v u₃ hu hv hw := sigmaTransition_comp D N κ q u v u₃ hu hv hw

/-- The transitions of `AlgebraicGeometry.sigmaDescentData` are the glued transitions. -/
public theorem sigmaDescentData_hom (k l : PUnit.{1}) {V : Scheme.{u}} (q : V ⟶ T)
    (u v : V ⟶ ∐ X) (hu : u ≫ Sigma.desc f = q) (hv : v ≫ Sigma.desc f = q) :
    (sigmaDescentData D N κ).hom (i₁ := k) (i₂ := l) q u v hu hv =
      sigmaTransition D N κ q u v hu hv := rfl

/-- The comparison at a factorization through an identity is the pullback of the comparison at the
identity. -/
public theorem pullModComp_id_hom {V Y : Scheme.{u}} (a : V ⟶ Y)
    (M : modulePullbackPseudofunctor.obj (.mk (op Y))) :
    (pullModComp a (𝟙 Y) a (Category.comp_id a) M).hom =
      (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.map (pullModId Y M).inv := by
  simp [pullModComp, pullModId, Pseudofunctor.mapComp'_id_comp_hom_app]
  rfl

/-- The comparison at a morphism into a summand, unfolded. -/
public theorem summandCompAt_hom {V : Scheme.{u}} {i : I} (a : V ⟶ X i) (u : V ⟶ ∐ X)
    (hu : a ≫ Sigma.ι X i = u) : (summandCompAt D N κ a u hu).hom =
      pullHom (summandBaseIso D N κ i).hom a u a hu (Category.comp_id a) := rfl

/-- The comparison at a morphism into a summand is the pullback of the comparison at the summand,
up to the comparison isomorphism of the pseudofunctor at the factorization. -/
public theorem summandCompAt_hom_eq {V : Scheme.{u}} {i : I} (a : V ⟶ X i) :
    (summandCompAt D N κ a (a ≫ Sigma.ι X i) rfl).hom =
      (pullModComp a (Sigma.ι X i) (a ≫ Sigma.ι X i) rfl N).hom ≫
        (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.map (κ i).hom := by
  rw [summandCompAt_hom, pullHom_eq_conj, summandBaseIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc, ← pullModComp_id_hom, Iso.hom_inv_id, Category.comp_id]

/-- The inverse form of `AlgebraicGeometry.summandCompAt_hom_eq`. -/
public theorem summandCompAt_inv_eq {V : Scheme.{u}} {i : I} (a : V ⟶ X i) :
    (summandCompAt D N κ a (a ≫ Sigma.ι X i) rfl).inv =
      (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.map (κ i).inv ≫
        (pullModComp a (Sigma.ι X i) (a ≫ Sigma.ι X i) rfl N).inv := by
  rw [← cancel_epi (summandCompAt D N κ a (a ≫ Sigma.ι X i) rfl).hom, Iso.hom_inv_id,
    summandCompAt_hom_eq, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

/-- The glued transition at the tautological factorizations is the transition of `D` conjugated by
the comparisons. -/
public theorem sigmaTransition_eq_summandTransition {V : Scheme.{u}} (q : V ⟶ T) {i j : I}
    (f₁ : V ⟶ X i) (f₂ : V ⟶ X j) (hu : (f₁ ≫ Sigma.ι X i) ≫ Sigma.desc f = q)
    (hv : (f₂ ≫ Sigma.ι X j) ≫ Sigma.desc f = q) (ha : f₁ ≫ f i = q) (hb : f₂ ≫ f j = q) :
    sigmaTransition D N κ q (f₁ ≫ Sigma.ι X i) (f₂ ≫ Sigma.ι X j) hu hv =
      (summandCompAt D N κ f₁ (f₁ ≫ Sigma.ι X i) rfl).hom ≫ D.obj.hom q f₁ f₂ ha hb ≫
        (summandCompAt D N κ f₂ (f₂ ≫ Sigma.ι X j) rfl).inv := by
  rw [← pullHom_id (sigmaTransition D N κ q (f₁ ≫ Sigma.ι X i) (f₂ ≫ Sigma.ι X j) hu hv),
    pullHom_sigmaTransition D N κ q _ _ hu hv (𝟙 V) (f₁ ≫ Sigma.ι X i) (f₂ ≫ Sigma.ι X j)
      (Category.id_comp _) (Category.id_comp _) f₁ f₂ rfl rfl]
  apply summandTransition_congr

/-- The glued transition at the tautological factorizations, written out in terms of the comparison
`κ`. -/
public theorem sigmaTransition_eq {V : Scheme.{u}} (q : V ⟶ T) {i j : I} (f₁ : V ⟶ X i)
    (f₂ : V ⟶ X j) (hu : (f₁ ≫ Sigma.ι X i) ≫ Sigma.desc f = q)
    (hv : (f₂ ≫ Sigma.ι X j) ≫ Sigma.desc f = q) (ha : f₁ ≫ f i = q) (hb : f₂ ≫ f j = q) :
    sigmaTransition D N κ q (f₁ ≫ Sigma.ι X i) (f₂ ≫ Sigma.ι X j) hu hv =
      (pullModComp f₁ (Sigma.ι X i) (f₁ ≫ Sigma.ι X i) rfl N).hom ≫
        (modulePullbackPseudofunctor.map f₁.op.toLoc).toFunctor.map (κ i).hom ≫
          D.obj.hom q f₁ f₂ ha hb ≫
            (modulePullbackPseudofunctor.map f₂.op.toLoc).toFunctor.map (κ j).inv ≫
              (pullModComp f₂ (Sigma.ι X j) (f₂ ≫ Sigma.ι X j) rfl N).inv := by
  rw [sigmaTransition_eq_summandTransition D N κ q f₁ f₂ hu hv ha hb, summandCompAt_hom_eq,
    summandCompAt_inv_eq, Category.assoc]

/-- The comparison `κ` is compatible with the glued transitions. -/
public theorem map_kappa_comp_hom {V : Scheme.{u}} (q : V ⟶ T) {i j : I} (f₁ : V ⟶ X i)
    (f₂ : V ⟶ X j) (hu : (f₁ ≫ Sigma.ι X i) ≫ Sigma.desc f = q)
    (hv : (f₂ ≫ Sigma.ι X j) ≫ Sigma.desc f = q) (ha : f₁ ≫ f i = q) (hb : f₂ ≫ f j = q) :
    (modulePullbackPseudofunctor.map f₁.op.toLoc).toFunctor.map (κ i).hom ≫
        D.obj.hom q f₁ f₂ ha hb =
      ((pullModComp f₁ (Sigma.ι X i) (f₁ ≫ Sigma.ι X i) rfl N).inv ≫
          sigmaTransition D N κ q (f₁ ≫ Sigma.ι X i) (f₂ ≫ Sigma.ι X j) hu hv ≫
            (pullModComp f₂ (Sigma.ι X j) (f₂ ≫ Sigma.ι X j) rfl N).hom) ≫
        (modulePullbackPseudofunctor.map f₂.op.toLoc).toFunctor.map (κ j).hom := by
  rw [sigmaTransition_eq D N κ q f₁ f₂ hu hv ha hb]
  simp

end Summands

section Conclusion

open QuasicoherentDescentData

variable (𝒱 : PreZeroHypercover.{w} T) [Small.{u} 𝒱.I₀] (D : QuasicoherentDescentData 𝒱.f)
  (N : modulePullbackPseudofunctor.obj (.mk (op (∐ 𝒱.X))))
  (κ : ∀ i, pullMod (Sigma.ι 𝒱.X i) N ≅ D.component i) (hN : N.IsQuasicoherent)

/-- `AlgebraicGeometry.sigmaDescentData`, typed at the one-element family
`AlgebraicGeometry.QuasicoherentDescentData.sigmaFamily 𝒱`. -/
public noncomputable def sigmaFamilyDescentData :
    modulePullbackPseudofunctor.DescentData (sigmaFamily 𝒱).f :=
  sigmaDescentData D N κ

/-- The objectwise quasi-inverse of the coproduct refinement: the quasi-coherent descent datum for
the one-element family `{∐ 𝒱.X i ⟶ T}` whose sole component is a quasi-coherent module `N` on the
coproduct identified summand by summand with the components of `D`, and whose transition over a
scheme with two morphisms to the coproduct over `T` is the one glued from the transitions of `D`.
-/
public noncomputable def QuasicoherentDescentData.ofSummands :
    QuasicoherentDescentData (sigmaFamily 𝒱).f :=
  ⟨sigmaFamilyDescentData 𝒱 D N κ, fun _ ↦ hN⟩

/-- Restricting `AlgebraicGeometry.sigmaDescentData` along the coproduct refinement gives back `D`,
at the level of the pullback pseudofunctor's descent data. -/
public noncomputable def sigmaDescentDataPullIso :
    Pseudofunctor.DescentData.pullFunctorObj (toSigmaFamily 𝒱).w₀
        (sigmaFamilyDescentData 𝒱 D N κ) ≅ D.obj :=
  Pseudofunctor.DescentData.isoMk (fun i ↦ κ i) (fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ ↦ by
    have hu : (f₁ ≫ Sigma.ι 𝒱.X i₁) ≫ Sigma.desc 𝒱.f = q := by
      rw [Category.assoc, Sigma.ι_comp_desc]; exact hf₁
    have hv : (f₂ ≫ Sigma.ι 𝒱.X i₂) ≫ Sigma.desc 𝒱.f = q := by
      rw [Category.assoc, Sigma.ι_comp_desc]; exact hf₂
    rw [Pseudofunctor.DescentData.pullFunctorObj_hom,
      Pseudofunctor.DescentData.pullFunctorObjHom_eq (toSigmaFamily 𝒱).w₀
        (sigmaFamilyDescentData 𝒱 D N κ) (f₁ ≫ 𝒱.f i₁) f₁ f₂ q (f₁ ≫ Sigma.ι 𝒱.X i₁)
        (f₂ ≫ Sigma.ι 𝒱.X i₂) rfl (hf₂.trans hf₁.symm)
        (by rw [Category.comp_id]; exact hf₁) rfl rfl]
    exact map_kappa_comp_hom D N κ q f₁ f₂ hu hv hf₁ hf₂)

/-- The comparison isomorphism of the objectwise quasi-inverse: restricting
`AlgebraicGeometry.QuasicoherentDescentData.ofSummands` along the coproduct refinement gives back
the original datum. -/
public noncomputable def QuasicoherentDescentData.ofSummandsIso :
    (pullFunctor (toSigmaFamily 𝒱)).obj (ofSummands 𝒱 D N κ hN) ≅ D :=
  ObjectProperty.isoMk
    (P := fun D : modulePullbackPseudofunctor.DescentData 𝒱.f ↦
      ∀ i, (D.obj i).IsQuasicoherent)
    (sigmaDescentDataPullIso 𝒱 D N κ)

/-- Every quasi-coherent descent datum for a family `{X i ⟶ T}` is the restriction of one for the
one-element family `{∐ X i ⟶ T}`, up to isomorphism. -/
public theorem QuasicoherentDescentData.essSurj_pullFunctor_toSigmaFamily :
    (pullFunctor (toSigmaFamily 𝒱)).EssSurj where
  mem_essImage D := by
    obtain ⟨M, ⟨e⟩⟩ := isEffective_restrictToSummands D
    have e' := (ObjectProperty.ι (fun D : modulePullbackPseudofunctor.DescentData
      (fun i ↦ Sigma.ι 𝒱.X i) ↦ ∀ i, (D.obj i).IsQuasicoherent)).mapIso e
    refine ⟨ofSummands 𝒱 D M.obj (fun i ↦ ⟨e'.hom.hom i, e'.inv.hom i, ?_, ?_⟩) M.property,
      ⟨ofSummandsIso 𝒱 D M.obj _ M.property⟩⟩
    · exact congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i) e'.hom_inv_id
    · exact congrArg (fun η ↦ Pseudofunctor.DescentData.Hom.hom η i) e'.inv_hom_id

/-- Restriction of quasi-coherent descent data along the coproduct refinement of a standard fpqc
covering of a spectrum is essentially surjective. -/
public theorem QuasicoherentDescentData.standardSigmaEssSurj : StandardSigmaEssSurj.{u} :=
  fun 𝒲 _ _ _ _ ↦ essSurj_pullFunctor_toSigmaFamily 𝒲

/-- Every quasi-coherent descent datum for a standard fpqc covering of `Spec R` (a finite jointly
surjective family of flat morphisms from affine schemes) is effective. -/
@[sga "4½ Arcata 1.4.5" "special case"]
public theorem QuasicoherentDescentData.isEffective_standardFpqc {R : CommRingCat.{u}}
    (𝒲 : PreZeroHypercover.{0} (Spec R)) [Finite 𝒲.I₀] [∀ i, IsAffine (𝒲.X i)]
    [∀ i, Flat (𝒲.f i)] (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ)
    (D : QuasicoherentDescentData 𝒲.f) : D.IsEffective :=
  isEffective_of_standardFpqc standardSigmaEssSurj 𝒲 hsurj D

/-- Every quasi-coherent descent datum for an *arbitrary* fpqc covering family of `Spec R` is
effective. -/
public theorem QuasicoherentDescentData.isEffective_fpqcPrecoverage_spec {R : CommRingCat.{u}}
    (𝒲 : PreZeroHypercover.{w} (Spec R))
    (h𝒲 : 𝒲.presieve₀ ∈ Scheme.fpqcPrecoverage (Spec R))
    (D : QuasicoherentDescentData 𝒲.f) : D.IsEffective :=
  isEffective_of_mem_fpqcPrecoverage_spec standardSigmaEssSurj 𝒲 h𝒲 D

/-- Assuming `AlgebraicGeometry.QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes`, every
quasi-coherent descent datum for an fpqc covering family of a scheme is effective. -/
public theorem QuasicoherentDescentData.isEffective_fpqcPrecoverage_of_globalizes
    (hglob : EffectiveOverSpecBaseGlobalizes.{w, u}) {S : Scheme.{u}}
    (𝒲 : PreZeroHypercover.{w} S) (h𝒲 : 𝒲.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (D : QuasicoherentDescentData 𝒲.f) : D.IsEffective :=
  isEffective_of_mem_fpqcPrecoverage standardSigmaEssSurj hglob 𝒲 h𝒲 D

end Conclusion

end QuasiInverse

end AlgebraicGeometry

end
