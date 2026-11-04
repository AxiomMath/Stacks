module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineSchemesOverCech
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfAnIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing

/-!
# Cohomology on affine objects of the big fppf site of an algebraic space, via Čech

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` one of its objects.
An object `U` of `(Spaces/X)_fppf` is *affine* (`BigFppfSpaceOver.IsAffineSchemeOver`) if its
algebraic space is represented by an affine scheme. A finite family of affine objects over an
affine object is an *affine fppf family* if, read through the representing schemes, it is an fppf
covering family of schemes. These families are cofinal among the coverings of affine objects, and
their fibre products are again affine; so by Stacks 03F9 an abelian sheaf whose restriction to the
affine schemes over every affine object is a base change presheaf `A ↦ 𝒪(A) ⊗ M` has no higher
cohomology on affine objects (the Čech cohomology of the base change presheaf vanishes by
Stacks 03FJ).

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.AffineFppfPresentation`: the data making a family of
  `(Spaces/X)_fppf` a finite fppf family of affine schemes over an affine scheme.
* `AlgebraicGeometry.BigFppfSpaceSite.affineFppfCoverings`: the finite affine fppf families.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.preservesPullbacks_toOver`: the
  embedding of the affine schemes over `U` into `(Spaces/X)_fppf` preserves fibre products.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_of_baseChange`: **vanishing of higher
  cohomology on affine objects** for an abelian sheaf which is a base change presheaf on the
  affine schemes over every affine object.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 0DGQ](https://stacks.math.columbia.edu/tag/0DGQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of schemes into algebraic spaces preserves fibre products.** -/
instance schemeSpaceFunctor_preservesLimitsOfShape_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (schemeSpaceFunctor B S hS) := by
  have : PreservesLimitsOfShape WalkingCospan
      (schemeSpaceFunctor B S hS ⋙ ObjectProperty.ι _) :=
    preservesLimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
        yoneda ≅ schemeSpaceFunctor B S hS ⋙ ObjectProperty.ι _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (ObjectProperty.ι _)

namespace BigFppfSpaceSite

variable {S} {T : BigFppfSpaceSite S} {X : T.Spaces}

namespace AffineSchemesOver

variable {U : BigFppfSpaceOver T X}

variable (T U) in
/-- The embedding of the affine schemes over `U` into `(Spaces/X)_fppf`. -/
abbrev toOver : AffineSchemesOver T U ⥤ Over X := toSlice T U ⋙ Over.forget U

variable (V₀ : T.Schemes)
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)

/-- The embedding of the affine schemes over `U`, followed by the forgetful functor to algebraic
spaces, read through the affine schemes over `V₀`. -/
noncomputable def toOverForgetIso :
    toAffineOverScheme V₀ e ⋙ (isAffineOverScheme T V₀).ι ⋙ Over.forget V₀ ⋙
        schemeSpaceFunctor T.schemeSite S T.scheme_mem ≅
      toOver T U ⋙ Over.forget X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

attribute [local instance] BigFppfSite.hasPullbacks_schemes in
include e in
/-- **The embedding of the affine schemes over `U` into `(Spaces/X)_fppf` preserves fibre
products**, when `U` is identified with the algebraic space of a scheme `V₀`. -/
theorem preservesPullbacks_toOver :
    PreservesLimitsOfShape WalkingCospan (toOver T U) := by
  have : PreservesLimitsOfShape WalkingCospan (toOver T U ⋙ Over.forget X) :=
    preservesLimitsOfShape_of_natIso (toOverForgetIso V₀ e)
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget X)

end AffineSchemesOver

/-- The data exhibiting a family of `(Spaces/X)_fppf` with target `U` as a family of affine
schemes over an affine scheme which is an fppf covering family of schemes. -/
structure AffineFppfPresentation {U : Over X} (E : PreZeroHypercover.{u + 1} U) where
  /-- The affine scheme representing the target. -/
  W : T.Schemes
  /-- The scheme underlying `W` is affine. -/
  isAffine_W : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W)
  /-- The identification of the target with the represented space. -/
  eW : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ U.left
  /-- The affine schemes representing the members. -/
  Y (i : E.I₀) : T.Schemes
  /-- The scheme underlying each `Y i` is affine. -/
  isAffine_Y (i : E.I₀) :
    IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Y i))
  /-- The identifications of the members with the represented spaces. -/
  eY (i : E.I₀) : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj (Y i) ≅ (E.X i).left
  /-- The morphisms of schemes representing the members of the family. -/
  φ (i : E.I₀) : Y i ⟶ W
  /-- Under the identifications `eY i` and `eW`, the morphism `φ i` represents `E.f i`. -/
  comm (i : E.I₀) : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (φ i) ≫ eW.hom =
    (eY i).hom ≫ (E.f i).left
  /-- The underlying morphisms of schemes form an fppf covering family of `W`. -/
  fppf : Presieve.ofArrows (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj (Y i))
      (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (φ i)) ∈
    Scheme.fppfPrecoverage ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W)

variable (T X) in
/-- **The finite affine fppf families** of `(Spaces/X)_fppf` with target `U`. -/
def affineFppfCoverings (U : Over X) :
    Set {E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ BigFppfSpaceOver.topology T X U} :=
  {E | Finite E.1.I₀ ∧ Nonempty (AffineFppfPresentation E.1)}

namespace AffineFppfPresentation

open AffineSchemesOver

variable {U : Over X} {E : PreZeroHypercover.{u + 1} U} (P : AffineFppfPresentation E)

/-- The target, as a terminal affine scheme over `U`. -/
abbrev base : AffineSchemesOver T U := ofIso P.W P.isAffine_W P.eW

/-- The family, as a family of affine schemes over `U`. -/
def family : PreZeroHypercover.{u + 1} P.base where
  I₀ := E.I₀
  X i := ⟨CostructuredArrow.mk ((P.eY i).hom ≫ (E.f i).left), P.isAffine_Y i⟩
  f i := ObjectProperty.homMk (CostructuredArrow.homMk (P.φ i) (P.comm i))

/-- The target of the family is identified with the image of the terminal affine scheme. -/
def baseIso : U ≅ (toOver T U).obj P.base :=
  Over.isoMk P.eW.symm (P.eW.inv_hom_id_assoc U.hom)

/-- The members of the family are identified with the images of the affine schemes. -/
def memberIso (i : E.I₀) : E.X i ≅ (toOver T U).obj (P.family.X i) :=
  Over.isoMk (P.eY i).symm (by
    change (P.eY i).inv ≫ ((P.eY i).hom ≫ (E.f i).left) ≫ U.hom = (E.X i).hom
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact Over.w (E.f i))

/-- The family is isomorphic, over `baseIso`, to the image of the family of affine schemes. -/
def homOver : E.HomOver (P.family.map (toOver T U)) P.baseIso.hom where
  s₀ i := i
  h₀ i := (P.memberIso i).hom
  w₀ i := by
    apply Over.OverMorphism.ext
    change (P.eY i).inv ≫ (schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (P.φ i) =
      (E.f i).left ≫ P.eW.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, ← P.comm i, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- The morphisms of `homOver` between the members are isomorphisms. -/
instance (i : E.I₀) : IsIso (P.homOver.h₀ i) :=
  inferInstanceAs (IsIso (P.memberIso i).hom)

/-- The map of index sets underlying `homOver` is bijective. -/
lemma bijective_homOver_s₀ : Function.Bijective P.homOver.s₀ :=
  Function.bijective_id

/-- The images in `(Spaces/X)_fppf` of the iterated fibre products of a finite affine fppf family
have products. -/
private theorem hasProduct_map_family :
    ∀ (n : ℕ) (i : Fin (n + 1) → (P.family.map (toOver T U)).I₀),
      HasProduct (fun a ↦ Over.mk ((P.family.map (toOver T U)).f (i a))) := by
  have := hasFiniteLimits P.W P.eW P.isAffine_W
  exact Stacks.Sites.hasProduct_fibreProducts _ (fun _ _ _ => inferInstance)

/-- The comparison map for the product of a finite affine fppf family, along the embedding of the
affine schemes into `(Spaces/X)_fppf`, is an isomorphism. -/
private theorem isIso_cechProductMapOfFunctor_family
    [∀ (n : ℕ) (i : Fin (n + 1) → P.family.I₀), HasProduct (fun a ↦ Over.mk (P.family.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → (P.family.map (toOver T U)).I₀),
      HasProduct (fun a ↦ Over.mk ((P.family.map (toOver T U)).f (i a)))]
    (n : ℕ) (i : Fin (n + 1) → P.family.I₀) :
    IsIso (Stacks.CechSite.cechProductMapOfFunctor (toOver T U) P.family n i) := by
  have := hasFiniteLimits P.W P.eW P.isAffine_W
  have := preservesPullbacks_toOver P.W P.eW
  have := Stacks.Sites.preservesLimit_fibreProducts_overPost (toOver T U) P.family
    (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) n i
  exact Stacks.CechSite.isIso_cechProductMapOfFunctor _ _ n i

/-- **Vanishing of positive Čech cohomology on a finite affine fppf family of `(Spaces/X)_fppf`.**
If the restriction of an abelian presheaf `G` to the affine schemes over the target is a base
change presheaf `A ↦ 𝒪(A) ⊗ M`, then the positive Čech cohomology of `G` on the family vanishes. -/
theorem isZero_cechCohomology_succ (G : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [Finite E.I₀]
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := U)).obj (op P.base)))
    (hM : (toOver T U).op ⋙ G ≅ ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
      (ringPresheaf (T := T) (V := U)) (isTerminalOfIso P.W P.isAffine_W P.eW)).obj M).presheaf)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (p : ℕ) : IsZero (Stacks.CechSite.cechCohomology E G (p + 1)) := by
  have := hasFiniteLimits P.W P.eW P.isAffine_W
  have : Finite P.family.I₀ := inferInstanceAs (Finite E.I₀)
  have := P.hasProduct_map_family
  have hiso := P.isIso_cechProductMapOfFunctor_family
  have h₀ : IsZero (Stacks.CechSite.cechCohomology P.family ((toOver T U).op ⋙ G) (p + 1)) :=
    (isZero_cechCohomology_baseChangePresheaf_succ P.W P.isAffine_W P.eW
      (isTerminalOfIso P.W P.isAffine_W P.eW) M P.family P.fppf p).of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (p + 1)).mapIso
        ((Stacks.CechSite.cechComplexFunctor P.family).mapIso hM))
  exact Stacks.CechSite.isZero_cechCohomology_of_isIso P.homOver P.bijective_homOver_s₀ G
    (p + 1) (h₀.of_iso (Stacks.CechSite.cechCohomologyIsoOfFunctor _ _ G hiso (p + 1)))

include P in
/-- **The iterated fibre products of a finite affine fppf family are affine objects.** -/
theorem isAffineSchemeOver_pi_left
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    BigFppfSpaceOver.IsAffineSchemeOver T X (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left := by
  have := hasFiniteLimits P.W P.eW P.isAffine_W
  have := P.hasProduct_map_family
  have := P.isIso_cechProductMapOfFunctor_family n i
  have := Stacks.CechSite.isIso_cechProductMapOfFunctor_left (toOver T U) P.family n i
  have := Stacks.CechSite.isIso_cechProductMap_of_isIso P.homOver n i
  let Q := (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left
  let e₁ := asIso (Stacks.CechSite.cechProductMap E (P.family.map (toOver T U)) P.homOver n i)
  let e₂ := asIso (Stacks.CechSite.cechProductMapOfFunctor (toOver T U) P.family n i).left
  exact ⟨Q.obj.left, Q.property, ⟨((Over.forget X).mapIso (e₁ ≪≫ e₂.symm)).symm⟩⟩

end AffineFppfPresentation

open AffineSchemesOver in
/-- **The finite affine fppf families are cofinal among the coverings of an affine object.** -/
theorem exists_affineFppfCoverings_le (U : Over X)
    (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U) (R : Sieve U)
    (hR : R ∈ BigFppfSpaceOver.topology T X U) :
    ∃ E ∈ affineFppfCoverings T X U, E.1.sieve₀ ≤ R := by
  obtain ⟨W, hW, ⟨eW⟩⟩ := hU
  let A₀ : AffineSchemesOver T U := ofIso W hW eW
  let ψ : (toOver T U).obj A₀ ⟶ U := Over.homMk eW.hom rfl
  have : IsIso ψ := inferInstanceAs (IsIso (Over.isoMk eW rfl :
    (toOver T U).obj A₀ ≅ U).hom)
  let R'' : Sieve ((toSlice T U).obj A₀) := (Sieve.overEquiv _).symm (R.pullback ψ)
  have hR'' : R'' ∈ ((BigFppfSpaceOver.topology T X).over U) ((toSlice T U).obj A₀) := by
    rw [GrothendieckTopology.mem_over_iff]
    refine ((Sieve.overEquiv ((toSlice T U).obj A₀)).apply_symm_apply (R.pullback ψ)).symm ▸ ?_
    exact (BigFppfSpaceOver.topology T X).pullback_stable ψ hR
  let R' : Sieve A₀ := R''.functorPullback (toSlice T U)
  have hR' : R' ∈ AffineSchemesOver.topology A₀ := by
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
    exact Functor.IsCoverDense.functorPullback_pushforward_covering ⟨R'', hR''⟩
  obtain ⟨n, Z, hZ, φ, hRφ, hcov, hfppf⟩ := exists_finite_fppf_ofArrows_le A₀ R' hR'
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := ULift.{u + 1} (Fin n)
      X := fun j => (toOver T U).obj
        ⟨CostructuredArrow.mk ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).map (φ j.down) ≫
          A₀.obj.hom), hZ j.down⟩
      f := fun j => (toOver T U).map (homOfScheme A₀ (hZ j.down) (φ j.down)) ≫ ψ }
  have hE : E.sieve₀ ∈ BigFppfSpaceOver.topology T X U := by
    rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := ψ)]
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense, Sieve.functorPushforward_ofArrows,
      GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hcov
    refine (BigFppfSpaceOver.topology T X).superset_covering ?_ hcov
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i => Sieve.ofArrows_mk (I := ULift.{u + 1} (Fin n)) E.X E.f ⟨i⟩
  refine ⟨⟨E, hE⟩, ⟨inferInstanceAs (Finite (ULift (Fin n))), ⟨?_⟩⟩, ?_⟩
  · exact
      { W := W
        isAffine_W := hW
        eW := eW
        Y := fun j => Z j.down
        isAffine_Y := fun j => hZ j.down
        eY := fun j => Iso.refl _
        φ := fun j => φ j.down
        comm := fun j => (Category.id_comp _).symm
        fppf := Presieve.ofArrows_comp_eq_of_surjective
            (fun i => (BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map (φ i))
            (a := ULift.down.{u + 1}) ULift.down_surjective ▸ hfppf }
  · exact (Sieve.generate_le_iff _ _).2 fun _ _ ⟨j⟩ => hRφ j.down

/-- The category of abelian sheaves on `(Spaces/X)_fppf` has `Ext` groups in the universe of the
morphisms of the site. -/
theorem hasExt_bigFppfSpaceOver :
    HasExt.{u + 1} (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse _

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **Higher cohomology of an abelian sheaf on `(Spaces/X)_fppf` vanishes on affine objects**,
when the sheaf is a base change presheaf `A ↦ 𝒪(A) ⊗ M` on the affine schemes over every affine
object. Here the affine objects range over a set `B` of affine objects closed under affine
objects mapping to them. -/
theorem isZero_H'_of_baseChange (B : Set (Over X))
    (hB : ∀ U ∈ B, BigFppfSpaceOver.IsAffineSchemeOver T X U)
    (hBdown : ∀ {U U' : Over X} (_ : U' ⟶ U), U ∈ B →
      BigFppfSpaceOver.IsAffineSchemeOver T X U' → U' ∈ B)
    (G : Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})
    (hG : ∀ U ∈ B, ∀ (W : T.Schemes)
      (hW : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W))
      (eW : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ U.left),
      ∃ M : ModuleCat.{u + 1} ((AffineSchemesOver.ringPresheaf (T := T) (V := U)).obj
          (op (AffineSchemesOver.ofIso W hW eW))),
        Nonempty ((AffineSchemesOver.toOver T U).op ⋙ G.obj ≅
          ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1}
            (AffineSchemesOver.ringPresheaf (T := T) (V := U))
            (AffineSchemesOver.isTerminalOfIso W hW eW)).obj M).presheaf))
    (U : Over X) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' G p U) := by
  have hProducts : ∀ {U : Over X}
      (E : {E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ BigFppfSpaceOver.topology T X U}),
      E ∈ {E | E ∈ affineFppfCoverings T X U ∧ U ∈ B} → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := fun E _ p i =>
    Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ => inferInstance) p i
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero.{u + 1, u + 1, u + 1}
    (BigFppfSpaceOver.topology T X) B (fun U => {E | E ∈ affineFppfCoverings T X U ∧ U ∈ B})
    hProducts ?_ ?_ G ?_ U hU p hp
  · rintro U E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    refine ⟨hU, fun i => hBdown (E.1.f i) hU ⟨P.Y i, P.isAffine_Y i, ⟨P.eY i⟩⟩,
      fun p i => ?_⟩
    have := hProducts E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    exact hBdown (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).hom hU (P.isAffineSchemeOver_pi_left p i)
  · intro U hU R hR
    obtain ⟨E, hE, hle⟩ := exists_affineFppfCoverings_le U (hB U hU) R hR
    exact ⟨E, ⟨hE, hU⟩, hle⟩
  · rintro U E ⟨⟨hfin, ⟨P⟩⟩, hU⟩ p hp
    have := hProducts E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    obtain ⟨M, ⟨hM⟩⟩ := hG U hU P.W P.isAffine_W P.eW
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
    have : Finite E.1.I₀ := hfin
    exact P.isZero_cechCohomology_succ G.obj M hM q

end BigFppfSpaceSite

end AlgebraicGeometry

end
