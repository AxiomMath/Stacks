module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineImageCover
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsDerivation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import StacksCore.Tactic.StacksAttribute

/-!
# The associated module of differentials corepresents the derivations of the small étale site

Let `f : X ⟶ Y` be a morphism of schemes.  Stacks 04CS asserts that the small-étale sheaf
`(Ω_{X/Y})^a` associated to the quasi-coherent module `Ω_{X/Y}` *is* the module of differentials
of the induced morphism of small étale sites, compatibly with the universal derivations.  The
two ingredients of the source's proof are already available: the comparison map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕` of a derivation `D` of `𝒪_{X_étale}` annihilating the functions pulled
back from `Y` is `AlgebraicGeometry.SmallEtale.differentialsComparison`, and the derivation
`d^a` of `(Ω_{X/Y})^a` is
`AlgebraicGeometry.SmallEtale.associatedRelativeDifferentialsDerivation`.  This module proves
that they are mutually inverse, in the form of the universal property: every such derivation
factors through `d^a` by a unique morphism of sheaves of modules.

Three things are proved, in this order.

**The restriction to the small Zariski site is injective.**  A derivation of `𝒪_{X_étale}` is
determined by its values on the global functions of the open subschemes of `X`.  This is the
only non-formal input and the reason an étale site appears at all: over an object `h : T → X` of
the small étale site, two derivations agreeing on the opens of `X` differ by a derivation of
`𝒪_T` relative to `𝒪_X`, and `Γ(U) ⟶ Γ(V)` is étale on the affine objects with affine image
which cover `T`, so that difference is a derivation along a formally unramified ring map and
hence zero.  The sheaf condition on the coefficients glues the vanishing back up.

**`d^a` is a `Y`-derivation and restricts to `d_{X/Y}`.**  The first is the hypothesis `hD` of
`differentialsComparison` at `D = d^a`, and the second says that the small Zariski restriction
of `d^a` is the universal derivation of `Ω_{X/Y}` followed by the unit of the adjunction of
Stacks 03DU (4) — equivalently, that `c''` at `d^a` is the identity.

**Corepresentability.**  Those two facts combine: existence of the factorization is the
comparison map, and both its uniqueness and the identity it satisfies come from the injectivity
of the Zariski restriction.

## Main results

* `AlgebraicGeometry.SmallEtale.eq_of_zariskiRestriction_eq`: **the injectivity**.  Two
  derivations of `𝒪_{X_étale}` with the same small Zariski restriction are equal.
* `AlgebraicGeometry.SmallEtale.eq_of_differentialsComparison_eq`: consequently the comparison
  map of Stacks 04CS determines the derivation it was formed from.
* `AlgebraicGeometry.SmallEtale.associatedRelativeDifferentialsDerivation_pullbackSection`: the
  derivation `d^a` annihilates every function pulled back from an open of `Y`, so the comparison
  map may be formed at `d^a`.
* `AlgebraicGeometry.SmallEtale.differentialsComparison_associatedRelativeDifferentialsDerivation`:
  the comparison map at `d^a` is the identity.
* `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedRelativeDifferentialsDerivation`:
  **Stacks 04CS**, corepresentability.  `(Ω_{X/Y})^a` together with `d^a` is the module of
  differentials of `𝒪_{X_étale}` over `Y`: every derivation of `𝒪_{X_étale}` annihilating the
  functions pulled back from `Y` factors through `d^a` by exactly one morphism of sheaves of
  modules.
* `AlgebraicGeometry.SmallEtale.isIso_differentialsComparison_of_universal`: therefore the
  comparison map into any *universal* such derivation is an isomorphism, which is the
  identification `Ω_{X_étale/Y_étale} ≅ (Ω_{X/Y})^a` of the source.

## Implementation notes

`AlgebraicGeometry.addMonoidHom_eq_zero_of_formallyUnramified` restates, for a bare additive map
satisfying the Leibniz rule, the vanishing of a derivation along a formally unramified ring map.
The same statement for `CategoryTheory.ModuleCat.Derivation` is `private` in
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/FormallyUnramified.lean`, and a private
name is not usable from another module; the proof here is the same five lines, routed through
`CategoryTheory.ModuleCat.Derivation.mk`.  Likewise
`AlgebraicGeometry.opens_ι_appLE_top` restates the identification of
`AlgebraicGeometry.Scheme.Hom.appLE` of an open immersion with
`AlgebraicGeometry.Scheme.Opens.topIso`.

The covering used for the injectivity is
`AlgebraicGeometry.SmallEtale.affineImageCover`, whose members are affine with affine image, so
that both ends of the ring map `Γ(U) ⟶ Γ(V)` are global sections of affine schemes and
`AlgebraicGeometry.FormallyUnramified.formallyUnramified_appLE` applies.  The structure
morphism of a member factors through the image by
`AlgebraicGeometry.SmallEtale.homOfRangeLe`, and that factorization is formally unramified by
cancellation, `AlgebraicGeometry.FormallyUnramified.of_comp`, against the open immersion of the
image.

Several of the proofs below compose morphisms by `Eq.trans` and `congrArg` where a `rw` would
read better.  That is forced: `TopCat.Sheaf` is a `def` rather than an abbreviation, so a
rewrite whose motive mentions `X.Modules` fails to elaborate, while `exact`-style application
unifies the two spellings at default transparency.  The same issue is documented in
`StacksFrontier/Topology/Sheaves/Modules/Differentials.lean`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site, whose universal property is
  the statement proved here.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), that an étale morphism
  does not change relative differentials.
* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4), that an unramified ring
  map has no nonzero derivations.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module
  on the small étale site and its right adjoint, and
  [Tag 070S](https://stacks.math.columbia.edu/tag/070S), that it is computed by the sections
  formula.
-/

@[expose] public section

open CategoryTheory Opposite Stacks.Sites AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry

/-- **A derivation along a formally unramified ring map is zero**, for an additive map satisfying
the Leibniz rule and annihilating the image of the base ring.  It factors through the module of
Kähler differentials, which is trivial.

This restates, for a bare `AddMonoidHom`, the private lemma
`moduleCatDerivation_d_eq_zero_of_formallyUnramified` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/FormallyUnramified.lean`. -/
public theorem addMonoidHom_eq_zero_of_formallyUnramified {A Bb : CommRingCat.{u}} (g : A ⟶ Bb)
    (hg : g.hom.FormallyUnramified) {M : ModuleCat.{u} Bb} (δ : Bb →+ M)
    (hmul : ∀ x y : Bb, δ (x * y) = x • δ y + y • δ x)
    (hvanish : ∀ x : A, δ (g x) = 0) (b : Bb) : δ b = 0 := by
  let D : M.Derivation g := ModuleCat.Derivation.mk δ (fun x y => δ.map_add x y) hmul hvanish
  let := g.hom.toAlgebra
  let := Module.compHom M g.hom
  have hfu : Algebra.FormallyUnramified A Bb := by
    rwa [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
  have : IsScalarTower A Bb M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Subsingleton (KaehlerDifferential A Bb) := (Algebra.formallyUnramified_iff A Bb).mp hfu
  let D' : Derivation A Bb M := D
  have h := congrArg
    (fun L : KaehlerDifferential A Bb →ₗ[Bb] M => L (KaehlerDifferential.D A Bb b))
    (Subsingleton.elim D'.liftKaehlerDifferential (0 : KaehlerDifferential A Bb →ₗ[Bb] M))
  exact (show D' b = 0 by simpa using h)

/-- The inclusion of an open subscheme, on sections over that open, is
`AlgebraicGeometry.Scheme.Opens.topIso`.  A restatement of `ι_appLE_top` of
`StacksFrontier/AlgebraicGeometry/ChartDictionary/Basic.lean`, which this module does not
import. -/
public theorem opens_ι_appLE_top {X : Scheme.{u}} (U : X.Opens)
    (e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : U.ι.appLE U ⊤ e = U.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

/-! ### The small Zariski restriction of a derivation determines it -/

section Injectivity

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R₁ R₂ : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ₁ : R₁ ⟶ (commRingStructureSheaf B X hX).obj}
  {ψ₂ : R₂ ⟶ (commRingStructureSheaf B X hX).obj}
  (D₁ : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val ψ₁)
  (D₂ : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val ψ₂)

/-- **Two derivations of `𝒪_{X_étale}` agreeing over the opens of `X` agree over an affine
object with affine image.**  Their difference is an additive map satisfying the Leibniz rule and
annihilating the image of `Γ(U, 𝒪_U)`, where `U` is an affine open of `X` through which the
structure morphism factors; that ring map is formally unramified because the structure morphism
is étale and the open immersion of `U` cancels, so the difference vanishes. -/
public theorem d_eq_of_hom_opensToSmallEtale
    (hagree : ∀ (U : X.Opens) (x : (commRingStructureSheaf B X hX).obj.obj
        (op ((opensToSmallEtale B X hX).obj U))), D₁.d x = D₂.d x)
    {T : SmallEtale B X hX} {U : X.Opens} (j : T ⟶ (opensToSmallEtale B X hX).obj U)
    (hU : IsAffineOpen U) (hT : _root_.AlgebraicGeometry.IsAffine ((toScheme B X hX).obj T))
    (a : (commRingStructureSheaf B X hX).obj.obj (op T)) :
    D₁.d a = D₂.d a := by
  have hAU : _root_.AlgebraicGeometry.IsAffine
    ((toScheme B X hX).obj ((opensToSmallEtale B X hX).obj U)) := hU
  have hfac : (toScheme B X hX).map j ≫ U.ι = ((toOver B X hX).obj T).hom :=
    (BigEtaleOver.hom_hom_eq B X hX j.hom).symm
  have hetT : Etale ((toOver B X hX).obj T).hom := T.property
  have h1 : FormallyUnramified ((toScheme B X hX).map j ≫ U.ι) :=
    hfac ▸ (inferInstance : FormallyUnramified ((toOver B X hX).obj T).hom)
  have h2 : FormallyUnramified ((toScheme B X hX).map j) :=
    FormallyUnramified.of_comp _ U.ι
  have h3 := ((toScheme B X hX).map j).formallyUnramified_appLE
    (isAffineOpen_top ((toScheme B X hX).obj ((opensToSmallEtale B X hX).obj U)))
    (isAffineOpen_top ((toScheme B X hX).obj T)) le_rfl
  have he : (commRingStructureSheaf B X hX).obj.map j.op
      = ((toScheme B X hX).map j).appLE ⊤ ⊤ le_rfl :=
    (Scheme.Γ_map_op _).trans (Scheme.Hom.appLE_eq_app _).symm
  have hfu : ((commRingStructureSheaf B X hX).obj.map j.op).hom.FormallyUnramified := by
    rwa [he]
  have key := addMonoidHom_eq_zero_of_formallyUnramified
    ((commRingStructureSheaf B X hX).obj.map j.op) hfu
    (D₁.d (X := op T) - D₂.d (X := op T)) ?_ ?_ a
  · rwa [AddMonoidHom.sub_apply, sub_eq_zero] at key
  · intro x y
    simp only [AddMonoidHom.sub_apply, D₁.d_mul, D₂.d_mul, smul_sub]
    abel
  · intro x
    simp only [AddMonoidHom.sub_apply]
    rw [D₁.d_map j.op x, D₂.d_map j.op x, hagree U x]
    exact sub_self _

/-- **Two derivations of `𝒪_{X_étale}` agreeing over the opens of `X` are equal.**  They agree
over the affine objects with affine image, which cover every object of the small étale site, and
the coefficient sheaf is separated. -/
public theorem d_eq_of_agree_opensToSmallEtale
    (hagree : ∀ (U : X.Opens) (x : (commRingStructureSheaf B X hX).obj.obj
        (op ((opensToSmallEtale B X hX).obj U))), D₁.d x = D₂.d x)
    (T : SmallEtale B X hX) (a : (commRingStructureSheaf B X hX).obj.obj (op T)) :
    D₁.d (X := op T) a = D₂.d (X := op T) a := by
  refine F.isSheaf.isSeparated T (affineImageCover B X hX T).sieve₀
    (mem_topology_sieve₀_affineImageCover B X hX T) (D₁.d a) (D₂.d a) ?_
  rintro Y g ⟨Z, h, p, ⟨i⟩, rfl⟩
  have hloc : D₁.d (X := op ((affineImageCover B X hX T).X i))
      ((commRingStructureSheaf B X hX).obj.map ((affineImageCover B X hX T).f i).op a) =
      D₂.d ((commRingStructureSheaf B X hX).obj.map ((affineImageCover B X hX T).f i).op a) :=
    d_eq_of_hom_opensToSmallEtale B hX D₁ D₂ hagree
      (homOfRangeLe B X hX (i.down.2.1 : X.Opens) (range_affineImageCover_X B X hX T i).le)
      i.down.2.2.2.1 (isAffine_affineImageCover_X B X hX T i) _
  have hstep := (D₁.d_map ((affineImageCover B X hX T).f i).op a).symm.trans
    (hloc.trans (D₂.d_map ((affineImageCover B X hX T).f i).op a))
  have hA : (F.val.presheaf.map ((affineImageCover B X hX T).f i).op) (D₁.d a)
      = (F.val.presheaf.map ((affineImageCover B X hX T).f i).op) (D₂.d a) := hstep
  rw [op_comp, F.val.presheaf.map_comp]
  exact congrArg (ConcreteCategory.hom (F.val.presheaf.map h.op)) hA

/-- **A derivation of `𝒪_{X_étale}` is determined by its small Zariski restriction**, in applied
form: if two derivations agree on the global functions of every open subscheme of `X`, they agree
over every object of the small étale site. -/
public theorem d_eq_of_zariskiRestrictionData_eq
    (h : ∀ (W : X.Opens) (b : Γ(X, W)),
      D₁.d (X := op ((opensToSmallEtale B X hX).obj W))
          (((commRingStructureMap B X hX).hom.app (op W)).hom b) =
        D₂.d (X := op ((opensToSmallEtale B X hX).obj W))
          (((commRingStructureMap B X hX).hom.app (op W)).hom b))
    (T : SmallEtale B X hX) (a : (commRingStructureSheaf B X hX).obj.obj (op T)) :
    D₁.d (X := op T) a = D₂.d (X := op T) a := by
  refine d_eq_of_agree_opensToSmallEtale B hX D₁ D₂ (fun U x => ?_) T a
  obtain ⟨b, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso ((Scheme.Opens.topIso U).inv)).2 x
  exact h U b

end Injectivity

section SameRelativeStructure

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X)
  {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}
  (E₁ E₂ : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj)
    F.val ψ)

/-- **The small Zariski restriction of a derivation of `𝒪_{X_étale}` determines it**, as bare
derivation data. -/
public theorem eq_of_zariskiRestrictionData_eq
    (h : zariskiRestrictionData B hX E₁ = zariskiRestrictionData B hX E₂) : E₁ = E₂ := by
  ext T a
  refine d_eq_of_zariskiRestrictionData_eq B hX E₁ E₂ (fun W b => ?_) T.unop a
  exact PresheafOfModulesOfCommRing.Derivation.congr_d h (X := op W) b

/-- **Restriction to the small Zariski site of `X` is injective on derivations of
`𝒪_{X_étale}`.** -/
public theorem zariskiRestrictionData_injective :
    Function.Injective (fun E : PresheafOfModulesOfCommRing.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val ψ => zariskiRestrictionData B hX E) :=
  fun _ _ h => eq_of_zariskiRestrictionData_eq B hX _ _ h

variable (f : X ⟶ Y)

/-- **Stacks 04CS, the injectivity step.**  A derivation of `𝒪_{X_étale}` annihilating the
functions pulled back from `Y` is determined by its restriction to the small Zariski site of
`X`.  Over an affine object with affine image the difference of two such derivations is a
derivation along an étale, hence formally unramified, ring map; those objects cover, and the
coefficient sheaf is separated. -/
public theorem eq_of_zariskiRestriction_eq
    (hE₁ : ∀ (W : Y.Opens) (b : Γ(Y, W)), E₁.d (pullbackSection B hX f W b) = 0)
    (hE₂ : ∀ (W : Y.Opens) (b : Γ(Y, W)), E₂.d (pullbackSection B hX f W b) = 0)
    (h : zariskiRestriction B hX f E₁ hE₁ = zariskiRestriction B hX f E₂ hE₂) : E₁ = E₂ :=
  eq_of_zariskiRestrictionData_eq B hX E₁ E₂ (by
    ext W a
    exact PresheafOfModulesOfCommRing.Derivation.congr_d h (X := W) a)

/-- **Stacks 04CS, the comparison map determines the derivation.**  Two derivations of
`𝒪_{X_étale}` annihilating the functions pulled back from `Y` with the same comparison map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕` are equal: the comparison map is formed from the small Zariski
restriction, and that restriction is injective. -/
public theorem eq_of_differentialsComparison_eq
    (hE₁ : ∀ (W : Y.Opens) (b : Γ(Y, W)), E₁.d (pullbackSection B hX f W b) = 0)
    (hE₂ : ∀ (W : Y.Opens) (b : Γ(Y, W)), E₂.d (pullbackSection B hX f W b) = 0)
    (h : differentialsComparison B hX f E₁ hE₁ = differentialsComparison B hX f E₂ hE₂) :
    E₁ = E₂ := by
  refine eq_of_zariskiRestriction_eq B hX E₁ E₂ f hE₁ hE₂ ?_
  rw [← differentialsComparison_adjunct B hX f E₁ hE₁,
    ← differentialsComparison_adjunct B hX f E₂ hE₂, h]

end SameRelativeStructure

/-! ### The derivation `d^a` annihilates the functions pulled back from `Y` -/

section Vanishing

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- The derivation `d_{T/Y}` of the open subscheme `T = f⁻¹W` annihilates a function pulled back
from `W`.  This is `AlgebraicGeometry.SheafOfModules.d_comorphism_eq_zero` for the structure
morphism `f⁻¹W → Y`, transported from the open `(f⁻¹W → Y)⁻¹W` to the top open along the
restriction maps; the two opens are equal but not definitionally so. -/
public theorem sectionsDerivationHom_pullbackSection (W : Y.Opens) (b : Γ(Y, W)) :
    sectionsDerivationHom B hX f ((opensToSmallEtale B X hX).obj (f ⁻¹ᵁ W))
      (pullbackSection B hX f W b) = 0 := by
  refine differentialsEtaleComparison_app_injective B hX f _
    (Eq.trans ?_ (map_zero _).symm)
  rw [differentialsEtaleComparison_sectionsDerivationHom]
  have e : (⊤ : (f ⁻¹ᵁ W).toScheme.Opens) ≤ ((f ⁻¹ᵁ W).ι ≫ f) ⁻¹ᵁ W := by simp
  have hcom := SheafOfModules.d_comorphism_eq_zero ((f ⁻¹ᵁ W).ι ≫ f)
    (universalRelativeDerivation ((f ⁻¹ᵁ W).ι ≫ f)) W b
  have hmap := (universalRelativeDerivation ((f ⁻¹ᵁ W).ι ≫ f)).d_map
    (homOfLE e).op ((((f ⁻¹ᵁ W).ι ≫ f).app W).hom b)
  rw [hcom, map_zero] at hmap
  have h1 : f.app W ≫ (f ⁻¹ᵁ W).topIso.inv = ((f ⁻¹ᵁ W).ι ≫ f).appLE W ⊤ e := by
    refine Eq.trans ?_ (Scheme.Hom.comp_appLE (f ⁻¹ᵁ W).ι f W ⊤ e).symm
    exact congrArg (fun k => f.app W ≫ k) (opens_ι_appLE_top (f ⁻¹ᵁ W) _).symm
  have hpull : pullbackSection B hX f W b
      = (((f ⁻¹ᵁ W).toScheme.presheaf.map (homOfLE e).op)).hom
          ((Scheme.Hom.app ((f ⁻¹ᵁ W).ι ≫ f) W).hom b) :=
    congrArg (fun k : Γ(Y, W) ⟶ Γ((f ⁻¹ᵁ W).toScheme, ⊤) => k.hom b) h1
  rwa [hpull]

/-- The derivation `d^a` on the sections description of the associated module annihilates every
function pulled back from an open of `Y`. -/
public theorem sectionsDerivation_pullbackSection (W : Y.Opens) (b : Γ(Y, W)) :
    (sectionsDerivation B hX f).d (X := op ((opensToSmallEtale B X hX).obj (f ⁻¹ᵁ W)))
      (pullbackSection B hX f W b) = 0 :=
  sectionsDerivationHom_pullbackSection B hX f W b

/-- **`d^a` is a `Y`-derivation.**  The derivation `d^a` of `(Ω_{X/Y})^a` annihilates every
function pulled back from an open of `Y`, which is the hypothesis under which
`AlgebraicGeometry.SmallEtale.differentialsComparison` is formed.  So the comparison map may be
formed at `d^a` itself. -/
public theorem associatedRelativeDifferentialsDerivation_pullbackSection
    (W : Y.Opens) (b : Γ(Y, W)) :
    (associatedRelativeDifferentialsDerivation B hX f).d (pullbackSection B hX f W b) = 0 := by
  refine Eq.trans (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply _ _ _) ?_
  rw [sectionsDerivation_pullbackSection]
  exact map_zero _

end Vanishing

/-! ### The unit of the associated-module adjunction, on sections -/

section Unit

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The unit of the associated-module adjunction of Stacks 03DU (4) pulls sections back.**
Read through the identification of `𝓕^a` with the sections description of Stacks 03DU (4), the
unit `𝓕 ⟶ ε_*(𝓕^a)` is the map `AlgebraicGeometry.SmallEtale.sectionsUnit` which sends a section
of `𝓕` over an open `U` of `S` to its pullback to the open subscheme `U`.

The two left adjoints of restriction — the associated-module functor and the sheafification of
the presheaf-level pullback — are compared by `CategoryTheory.SheafOfModules.pullbackIso`, which
is `CategoryTheory.Adjunction.leftAdjointUniq`, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` carries the one unit to the other; the
remaining factor is cancelled by
`AlgebraicGeometry.Adjunction.unit_comp_map_unit_comp` together with
`AlgebraicGeometry.SmallEtale.unit_comp_map_sectionsComparison`. -/
public theorem val_unit_comp_restrictModule_map_associatedModuleIsoSections
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.Hom.val ((associatedModuleAdjunction B S hS).unit.app F ≫
      (restrictModule B S hS).map (associatedModuleIsoSectionsSheafOfModules' B S hS F).hom) =
      sectionsUnit B S hS F := by
  have hA := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS))
    (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)) F
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom)
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B S hS).obj))
      ((SheafOfModules.forget S.ringCatSheaf).obj F)
      (sectionsComparison B S hS F)
      (unit_comp_map_sectionsComparison B S hS F)
  have hu := isIso_sheafificationAdjunction_unit_app B S hS
    (sectionsPresheafOfModules B S hS F) (isSheaf_sectionsPresheafOfModules B S hS F)
  have hcounit : (PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureSheaf B S hS).obj)).counit.app (sectionsSheafOfModules' B S hS F) =
      (sheafificationSectionsIso B S hS F).hom := by
    refine (SheafOfModules.fullyFaithfulForget (structureSheaf B S hS)).map_injective ?_
    refine Eq.trans (IsIso.inv_eq_of_hom_inv_id
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureSheaf B S hS).obj)).right_triangle_components
          (Y := sectionsSheafOfModules' B S hS F))).symm ?_
    exact ((SheafOfModules.fullyFaithfulForget (structureSheaf B S hS)).map_preimage _).symm
  have hiso : (associatedModuleIsoSectionsSheafOfModules' B S hS F).hom =
      (((associatedModuleSheafificationIso B S hS).app F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
          (sectionsComparison B S hS F)) ≫
        (sheafificationSectionsIso B S hS F).hom :=
    Eq.trans (Category.assoc _ _ _).symm
      (congrArg (fun k => (((associatedModuleSheafificationIso B S hS).app F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
          (sectionsComparison B S hS F)) ≫ k) hcounit)
  have hA' : (associatedModuleAdjunction B S hS).unit.app F ≫
      (restrictModule B S hS).map ((associatedModuleSheafificationIso B S hS).app F).hom =
      (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)).unit.app F := hA
  rw [hiso, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hA']
  refine Eq.trans (show _ = (((SheafOfModules.forget S.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (structureMap B S hS)).unit.app F) ≫
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
        ((SheafOfModules.forget (structureSheaf B S hS) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (sectionsComparison B S hS F)))) ≫
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
        ((SheafOfModules.forget (structureSheaf B S hS) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          (sheafificationSectionsIso B S hS F).hom)) from rfl) ?_
  refine Eq.trans (congrArg (fun k => k ≫
    (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
      ((SheafOfModules.forget (structureSheaf B S hS) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          (sheafificationSectionsIso B S hS F).hom)) hkey) ?_
  have hCc : (SheafOfModules.forget (structureSheaf B S hS) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          (sheafificationSectionsIso B S hS F).hom =
      inv ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F)) :=
    (SheafOfModules.fullyFaithfulForget (structureSheaf B S hS)).map_preimage _
  have hfin : (PresheafOfModules.sheafificationAdjunction
        (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F) ≫
      (SheafOfModules.forget (structureSheaf B S hS) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          (sheafificationSectionsIso B S hS F).hom = 𝟙 _ :=
    Eq.trans (congrArg (fun k => (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F) ≫ k) hCc)
      (IsIso.hom_inv_id _)
  rw [Category.assoc, ← Functor.map_comp, hfin]
  refine Eq.trans (congrArg (fun k => sectionsUnit B S hS F ≫ k)
    (CategoryTheory.Functor.map_id
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom) _)) ?_
  exact Category.comp_id _

end Unit

/-! ### `d^a` restricts to the universal derivation of `Ω_{X/Y}` -/

section Restriction

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) {Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- **The characterization of `d^a` over an open subscheme of `X`.**  Over the object `U → X` of
the small étale site attached to an open `U` of `X`, the derivation `d^a` sends a global function
of `U` coming from `Γ(X, U)` to the pullback to `U` of its universal differential.  This is the
defining property of the canonical map of Stacks 01UV, read at the open immersion of `U` and
transported from the open `U.ι⁻¹U` to the top open. -/
public theorem sectionsDerivationHom_commRingStructureMap (W : X.Opens) (a : Γ(X, W)) :
    sectionsDerivationHom B hX f ((opensToSmallEtale B X hX).obj W)
        (((commRingStructureMap B X hX).hom.app (op W)).hom a) =
      pullbackSectionHom W.ι (relativeDifferentials f) W ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl)
        ((universalRelativeDerivation f).d a) := by
  refine (differentialsEtaleComparison_app_injective B hX f
    ((opensToSmallEtale B X hX).obj W) (Eq.trans ?_
      (differentialsEtaleComparison_sectionsDerivationHom B hX f
        ((opensToSmallEtale B X hX).obj W)
        (((commRingStructureMap B X hX).hom.app (op W)).hom a)).symm)).symm
  have hA := relativeDifferentialsMap_app_d (f := W.ι) (p := f) (p' := W.ι ≫ f) (𝟙 Y)
    (Category.comp_id _).symm W a
  rw [Adjunction.homEquiv_unit] at hA
  have hA2 : (Scheme.Modules.Hom.app
      (differentialsEtaleComparison B hX f ((opensToSmallEtale B X hX).obj W))
        (W.ι ⁻¹ᵁ W)).hom
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
        (relativeDifferentials f)) W).hom ((universalRelativeDerivation f).d a)) =
      (universalRelativeDerivation (W.ι ≫ f)).d ((W.ι.app W).hom a) := hA
  refine Eq.trans (Scheme.Modules.Hom.app_presheaf_map
    (differentialsEtaleComparison B hX f ((opensToSmallEtale B X hX).obj W))
    (homOfLE (Scheme.Opens.top_le_ι_preimage (le_refl W))) _) ?_
  refine Eq.trans (congrArg (fun z => ((relativeDifferentials (W.ι ≫ f)).presheaf.map
    (homOfLE (Scheme.Opens.top_le_ι_preimage (le_refl W))).op) z) hA2) ?_
  refine Eq.trans (((universalRelativeDerivation (W.ι ≫ f)).d_map
    (homOfLE (Scheme.Opens.top_le_ι_preimage (le_refl W))).op ((W.ι.app W).hom a)).symm) ?_
  exact congrArg (fun z => (universalRelativeDerivation (W.ι ≫ f)).d z)
    (congrArg (fun k : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) => k.hom a) (opens_ι_appLE_top W _))

/-- **The small Zariski restriction of `d^a` is the universal derivation of `Ω_{X/Y}` followed by
the unit of the associated-module adjunction.**  Over an open `U` of `X` both sides send a
function to the pullback to `U` of its universal differential: the left-hand side by
`AlgebraicGeometry.SmallEtale.val_unit_comp_restrictModule_map_associatedModuleIsoSections`, the
right-hand side by
`AlgebraicGeometry.SmallEtale.sectionsDerivationHom_commRingStructureMap`. -/
public theorem postcomp_homEquiv_id_eq_zariskiRestriction :
    (universalRelativeDerivation f).postcomp
      (((associatedModuleAdjunction B X hX).homEquiv (relativeDifferentials f)
        (associatedRelativeDifferentials B hX f))
          (𝟙 (associatedRelativeDifferentials B hX f))).val =
      zariskiRestriction B hX f (associatedRelativeDifferentialsDerivation B hX f)
        (associatedRelativeDifferentialsDerivation_pullbackSection B hX f) := by
  ext W a
  have hR : (zariskiRestriction B hX f (associatedRelativeDifferentialsDerivation B hX f)
        (associatedRelativeDifferentialsDerivation_pullbackSection B hX f)).d a =
      ((associatedModuleIsoSectionsSheafOfModules' B X hX (relativeDifferentials f)).inv.val.app
        (op ((opensToSmallEtale B X hX).obj W.unop))).hom
        (sectionsDerivationHom B hX f ((opensToSmallEtale B X hX).obj W.unop)
          (((commRingStructureMap B X hX).hom.app W).hom a)) := rfl
  have h2 : ((associatedModuleIsoSectionsSheafOfModules' B X hX
          (relativeDifferentials f)).hom.val.app
        (op ((opensToSmallEtale B X hX).obj W.unop))).hom
      ((((associatedModuleAdjunction B X hX).unit.app
        (relativeDifferentials f)).val.app W).hom
        ((universalRelativeDerivation f).d a)) =
      (sectionsUnitApp B X hX (relativeDifferentials f) W).hom
        ((universalRelativeDerivation f).d a) :=
    ConcreteCategory.congr_hom
      (congrArg (fun k => PresheafOfModules.Hom.app k W)
        (val_unit_comp_restrictModule_map_associatedModuleIsoSections B X hX
          (relativeDifferentials f)))
      ((universalRelativeDerivation f).d a)
  have hcancel : ∀ z, ((associatedModuleIsoSectionsSheafOfModules' B X hX
        (relativeDifferentials f)).inv.val.app
        (op ((opensToSmallEtale B X hX).obj W.unop))).hom
      (((associatedModuleIsoSectionsSheafOfModules' B X hX (relativeDifferentials f)).hom.val.app
        (op ((opensToSmallEtale B X hX).obj W.unop))).hom z) = z := by
    intro z
    exact ConcreteCategory.congr_hom
      (congrArg (fun k : associatedRelativeDifferentials B hX f ⟶
          associatedRelativeDifferentials B hX f =>
        PresheafOfModules.Hom.app k.val (op ((opensToSmallEtale B X hX).obj W.unop)))
        ((associatedModuleIsoSectionsSheafOfModules' B X hX
          (relativeDifferentials f)).hom_inv_id)) z
  refine Eq.trans (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply _ _ _) ?_
  refine Eq.trans (congrArg (fun k : relativeDifferentials f ⟶
      (restrictModule B X hX).obj (associatedRelativeDifferentials B hX f) =>
    ((k.val.app W).hom) ((universalRelativeDerivation f).d a))
    ((associatedModuleAdjunction B X hX).homEquiv_id (relativeDifferentials f))) ?_
  refine Eq.trans ?_ (Eq.trans (congrArg (fun z =>
    ((associatedModuleIsoSectionsSheafOfModules' B X hX (relativeDifferentials f)).inv.val.app
      (op ((opensToSmallEtale B X hX).obj W.unop))).hom z)
      (sectionsDerivationHom_commRingStructureMap B X hX f W.unop a).symm) hR.symm)
  refine Eq.trans ?_ (congrArg (fun z =>
    ((associatedModuleIsoSectionsSheafOfModules' B X hX (relativeDifferentials f)).inv.val.app
      (op ((opensToSmallEtale B X hX).obj W.unop))).hom z) h2)
  exact (hcancel _).symm

/-- **Stacks 04CS, the comparison map at `d^a` is the identity.**  The morphism
`c'' : (Ω_{X/Y})^a ⟶ (Ω_{X/Y})^a` attached to the derivation `d^a` is the identity, because the
small Zariski restriction of `d^a` is the universal derivation of `Ω_{X/Y}` followed by the unit
of the adjunction, and `c''` is the unique morphism with that property. -/
public theorem differentialsComparison_associatedRelativeDifferentialsDerivation :
    differentialsComparison B hX f (associatedRelativeDifferentialsDerivation B hX f)
        (associatedRelativeDifferentialsDerivation_pullbackSection B hX f) =
      𝟙 (associatedRelativeDifferentials B hX f) :=
  (eq_differentialsComparison B hX f (associatedRelativeDifferentialsDerivation B hX f)
    (associatedRelativeDifferentialsDerivation_pullbackSection B hX f) _
    (postcomp_homEquiv_id_eq_zariskiRestriction B X hX f)).symm

end Restriction

/-! ### Corepresentability -/

section Corepresentable

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) {Y : Scheme.{u}}
  (f : X ⟶ Y)

/-- Postcomposition of a derivation of a presheaf of modules is compatible with composition. -/
public theorem postcomp_postcomp {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {ψ : R₀ ⟶ R}
    (D : PresheafOfModulesOfCommRing.Derivation' M ψ) (α : M ⟶ N) (β : N ⟶ P) :
    (D.postcomp α).postcomp β = D.postcomp (α ≫ β) := by
  ext W a
  rfl

/-- Two successive postcompositions of a derivation, each with a known result, compose. -/
private theorem postcomp_comp_eq_of_postcomp_eq {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {ψ : R₀ ⟶ R}
    (D : PresheafOfModulesOfCommRing.Derivation' M ψ)
    {D' : PresheafOfModulesOfCommRing.Derivation' N ψ}
    {D'' : PresheafOfModulesOfCommRing.Derivation' P ψ} (α : M ⟶ N) (β : N ⟶ P)
    (h₁ : D.postcomp α = D') (h₂ : D'.postcomp β = D'') : D.postcomp (α ≫ β) = D'' := by
  rw [← postcomp_postcomp, h₁, h₂]

/-- Postcomposition of a derivation of a presheaf of modules by an identity changes nothing. -/
public theorem postcomp_id {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {ψ : R₀ ⟶ R}
    (D : PresheafOfModulesOfCommRing.Derivation' M ψ) : D.postcomp (𝟙 M) = D := by
  ext W a
  rfl

variable {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}

/-- The comparison map of Stacks 04CS depends on the derivation only, the vanishing hypothesis
being a proposition. -/
public theorem differentialsComparison_congr
    {E E' : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      F.val ψ}
    (hEE' : E = E')
    (hE : ∀ (W : Y.Opens) (b : Γ(Y, W)), E.d (pullbackSection B hX f W b) = 0)
    (hE' : ∀ (W : Y.Opens) (b : Γ(Y, W)), E'.d (pullbackSection B hX f W b) = 0) :
    differentialsComparison B hX f E hE = differentialsComparison B hX f E' hE' := by
  subst hEE'
  rfl

/-- **Stacks 04CS, the factorization.**  The comparison map `c''` of a derivation `D` of
`𝒪_{X_étale}` annihilating the functions pulled back from `Y` carries the derivation `d^a` of
`(Ω_{X/Y})^a` to `D`.

Both sides have the same small Zariski restriction — the comparison map's adjunct carries
`d_{X/Y}` to the restriction of `D`, and `d^a` restricts to `d_{X/Y}` followed by the unit of the
adjunction — and restriction is injective. -/
public theorem postcomp_differentialsComparison
    (D : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (constIntMap (commRingStructureSheaf B X hX).obj))
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    (associatedRelativeDifferentialsDerivation B hX f).postcomp
      (differentialsComparison B hX f D hD).val = D := by
  have h0 := associatedRelativeDifferentialsDerivation_pullbackSection B hX f
  have hid := differentialsComparison_associatedRelativeDifferentialsDerivation B X hX f
  have hzr : zariskiRestriction B hX f (associatedRelativeDifferentialsDerivation B hX f) h0 =
      (universalRelativeDerivation f).postcomp
        (((associatedModuleAdjunction B X hX).homEquiv
          (relativeDifferentials f) (associatedRelativeDifferentials B hX f))
            (𝟙 (associatedRelativeDifferentials B hX f))).val := by
    rw [← differentialsComparison_adjunct B hX f
      (associatedRelativeDifferentialsDerivation B hX f) h0, hid]
  have key : (zariskiRestriction B hX f (associatedRelativeDifferentialsDerivation B hX f)
        h0).postcomp (((restrictModule B X hX).map (differentialsComparison B hX f D hD))).val =
      zariskiRestriction B hX f D hD := by
    rw [hzr]
    refine Eq.trans (AlgebraicGeometry.SheafOfModules.postcomp_comp_val
      (universalRelativeDerivation f)
      (((associatedModuleAdjunction B X hX).homEquiv
        (relativeDifferentials f) (associatedRelativeDifferentials B hX f))
          (𝟙 (associatedRelativeDifferentials B hX f)))
      ((restrictModule B X hX).map (differentialsComparison B hX f D hD))) ?_
    rw [← differentialsComparison_adjunct B hX f D hD]
    refine congrArg (fun k : relativeDifferentials f ⟶
        (restrictModule B X hX).obj F =>
      (universalRelativeDerivation f).postcomp k.val) ?_
    refine Eq.trans (((associatedModuleAdjunction B X hX).homEquiv_naturality_right
      (𝟙 (associatedRelativeDifferentials B hX f))
      (differentialsComparison B hX f D hD)).symm) ?_
    exact congrArg _ (Category.id_comp (differentialsComparison B hX f D hD))
  refine eq_of_zariskiRestriction_eq B hX
    ((associatedRelativeDifferentialsDerivation B hX f).postcomp
      (differentialsComparison B hX f D hD).val) D f
    (postcomp_pullbackSection_eq_zero B hX f
      (associatedRelativeDifferentialsDerivation B hX f) h0
      (differentialsComparison B hX f D hD)) hD ?_
  rwa [← zariskiRestriction_postcomp B hX f
    (associatedRelativeDifferentialsDerivation B hX f) h0
    (differentialsComparison B hX f D hD)]

/-- **Stacks 04CS, the uniqueness of the factorization.**  A morphism out of `(Ω_{X/Y})^a` is
determined by its effect on the derivation `d^a`: the comparison map at `d^a` is the identity, so
the comparison map of the postcomposed derivation recovers the morphism. -/
public theorem hom_ext_associatedRelativeDifferentialsDerivation
    {G : SheafOfModules.{u} (structureSheaf B X hX)}
    {g₁ g₂ : associatedRelativeDifferentials B hX f ⟶ G}
    (h : (associatedRelativeDifferentialsDerivation B hX f).postcomp g₁.val =
      (associatedRelativeDifferentialsDerivation B hX f).postcomp g₂.val) : g₁ = g₂ := by
  have h0 := associatedRelativeDifferentialsDerivation_pullbackSection B hX f
  have hid := differentialsComparison_associatedRelativeDifferentialsDerivation B X hX f
  have hrec : ∀ g : associatedRelativeDifferentials B hX f ⟶ G,
      g = differentialsComparison B hX f
        ((associatedRelativeDifferentialsDerivation B hX f).postcomp g.val)
        (postcomp_pullbackSection_eq_zero B hX f
          (associatedRelativeDifferentialsDerivation B hX f) h0 g) := by
    intro g
    refine Eq.trans ?_ (differentialsComparison_postcomp B hX f
      (associatedRelativeDifferentialsDerivation B hX f) h0 g).symm
    rw [hid, Category.id_comp]
  refine Eq.trans (hrec g₁) (Eq.trans ?_ (hrec g₂).symm)
  exact differentialsComparison_congr B X hX f h _ _

/-- **Stacks 04CS.**  The associated module `(Ω_{X/Y})^a` of the relative differentials of
`f : X ⟶ Y`, together with the derivation `d^a`, is the module of differentials of
`𝒪_{X_étale}` over `Y` in the sense of Stacks 04BN: every derivation `D` of `𝒪_{X_étale}` with
values in a sheaf of `𝒪_{X_étale}`-modules `𝓖` which annihilates the functions pulled back from
`Y` factors as `D = d^a ∘ g` for exactly one morphism `g : (Ω_{X/Y})^a ⟶ 𝓖` of sheaves of
modules.

The factorization is the comparison map `c''` of
`AlgebraicGeometry.SmallEtale.differentialsComparison`; that it *is* a factorization, and that it
is the only one, both come from the injectivity of restriction to the small Zariski site
together with the identity
`AlgebraicGeometry.SmallEtale.differentialsComparison_associatedRelativeDifferentialsDerivation`.

The derivation is taken relative to the constant presheaf of integers, which imposes nothing
beyond the Leibniz rule, so that the `Y`-linearity is carried by the hypothesis `hD` alone; see
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentials.lean`. -/
@[stacks 04CS "corepresentability: `(Ω_{X/Y})^a` with `d^a` is the module of differentials"]
public theorem existsUnique_postcomp_associatedRelativeDifferentialsDerivation
    {G : SheafOfModules.{u} (structureSheaf B X hX)}
    (D : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) G.val
      (constIntMap (commRingStructureSheaf B X hX).obj))
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    ∃! g : associatedRelativeDifferentials B hX f ⟶ G,
      (associatedRelativeDifferentialsDerivation B hX f).postcomp g.val = D :=
  ⟨differentialsComparison B hX f D hD, postcomp_differentialsComparison B X hX f D hD,
    fun _ hg => hom_ext_associatedRelativeDifferentialsDerivation B X hX f
      (Eq.trans hg (postcomp_differentialsComparison B X hX f D hD).symm)⟩

/-- **Stacks 04CS, the isomorphism.**  Let `𝓕` with a derivation `D` of `𝒪_{X_étale}`
annihilating the functions pulled back from `Y` be *universal* among such derivations — that is,
let it be the module of differentials `Ω_{X_étale/Y_étale}` of Stacks 04BN.  Then the comparison
map `c'' : (Ω_{X/Y})^a ⟶ 𝓕` of Stacks 04CS is an isomorphism.

Both `(Ω_{X/Y})^a` with `d^a` and `𝓕` with `D` corepresent the same functor, so the
factorizations of each derivation through the other are mutually inverse, and the one out of
`(Ω_{X/Y})^a` is the comparison map by
`AlgebraicGeometry.SmallEtale.postcomp_differentialsComparison`. -/
public theorem isIso_differentialsComparison_of_universal
    (D : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) F.val
      (constIntMap (commRingStructureSheaf B X hX).obj))
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (huniv : ∀ (G : SheafOfModules.{u} (structureSheaf B X hX))
      (E : PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj) G.val
        (constIntMap (commRingStructureSheaf B X hX).obj)),
      (∀ (W : Y.Opens) (b : Γ(Y, W)), E.d (pullbackSection B hX f W b) = 0) →
        ∃! g : F ⟶ G, D.postcomp g.val = E) :
    IsIso (differentialsComparison B hX f D hD) := by
  obtain ⟨c, hc, -⟩ := huniv (associatedRelativeDifferentials B hX f)
    (associatedRelativeDifferentialsDerivation B hX f)
    (associatedRelativeDifferentialsDerivation_pullbackSection B hX f)
  obtain ⟨w, -, hFuniq⟩ := huniv F D hD
  refine ⟨c, ?_, ?_⟩
  · refine hom_ext_associatedRelativeDifferentialsDerivation B X hX f
      (Eq.trans ?_ (postcomp_id _).symm)
    exact postcomp_comp_eq_of_postcomp_eq _ _ _
      (postcomp_differentialsComparison B X hX f D hD) hc
  · refine Eq.trans (hFuniq _ ?_) (hFuniq _ (postcomp_id D)).symm
    exact postcomp_comp_eq_of_postcomp_eq _ _ _ hc
      (postcomp_differentialsComparison B X hX f D hD)

end Corepresentable

end AlgebraicGeometry.SmallEtale

end
