module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalClaims

/-!
# The diagonal argument of [Stacks, Tag 0G8J] in terms of cup products

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n = e + 1` with a section `σ`,
`W = X ×_A X` with projections `p₁`, `p₂`, `ξ = γ_σ(1)` the Gysin class of the section and
`η = γ_Δ(1)` that of the diagonal. Through [Stacks, Tag 0G8C] the two claims of
`StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalClaims` are statements about cup products on
`W`. This file states them, together with the statement of the factorization through the section
on which the first rests.

* `Stacks.WeilDeRham.StarIdentity`: `p₁^*θ ∪ η = p₁^*θ ∪ p₂^*ξ + p₂^*θ ∪ p₁^*ξ` in
  `H^{2n}(W, Ω^{2n-1}_{W/A})` for `θ ∈ Hⁿ(X, Ω^{n-1}_{X/A})`; this is the claim `θ₁ = θ₂ = θ` of
  the source.
* `Stacks.WeilDeRham.CupTopInjective`: `x ↦ p₂^*x ∪ p₁^*ξ` is injective on `Hⁿ(X, Ωⁿ_{X/A})`.
* `Stacks.WeilDeRham.CupFactorsThroughSection`: for maps `p q : W ⟶ X` and a section `j` of `q`,
  the cup product `p^*θ ∪ ε` of a class `ε ∈ Hⁿ(W, q^*G)` depends on `ε` only through `j^*ε`.

## Main definitions

* `Stacks.WeilDeRham.cupOnProduct`, `Stacks.WeilDeRham.fstPullback`,
  `Stacks.WeilDeRham.sndPullback`, `Stacks.WeilDeRham.diagonalClass`,
  `Stacks.WeilDeRham.fstSectionClass`, `Stacks.WeilDeRham.sndSectionClass`.
* `Stacks.WeilDeRham.unitPullback`, `Stacks.WeilDeRham.pullbackCup`.
* `Stacks.WeilDeRham.StarIdentity`, `Stacks.WeilDeRham.CupTopInjective`,
  `Stacks.WeilDeRham.CupFactorsThroughSection`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules (canonicalPairingModule)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-! ### Pullbacks along the unit and the cup product of pulled back classes -/

section General

variable {X W : Scheme.{u}}

/-- **The pullback `g^* : Hᵐ(X, F) ⟶ Hᵐ(W, g^*F)`** of [Stacks, Tag 01F9] along the unit
`F ⟶ g_*g^*F` of the adjunction `g^* ⊣ g_*`. -/
def unitPullback (g : W ⟶ X) (F : X.Modules) (m : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ m F ⟶
      Hgroup (structureSheafRing W.toRingedSpace) ⊤ m ((Scheme.Modules.pullback g).obj F) :=
  pullbackHgroup (CohomologyPullbackComparison.canonical g.toLRSHom.toShHom) 0 (m : ℤ) m
    (by simp) ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F)

/-- **The cup product `Hᵐ(W, p^*F) × Hⁿ(W, q^*G) ⟶ H^{m+n}(W, p^*F ⊗ q^*G)`** of Cohomology,
Section 0FKU on the ringed space `(W, 𝒪_W)`, along the identity of `p^*F ⊗ q^*G`, both classes
read through the bridge `hgroupModuleShiftIso`. -/
def pullbackCup (p q : W ⟶ X) (F G : X.Modules) (m n : ℕ)
    (a : Hgroup (structureSheafRing W.toRingedSpace) ⊤ m ((Scheme.Modules.pullback p).obj F))
    (b : Hgroup (structureSheafRing W.toRingedSpace) ⊤ n ((Scheme.Modules.pullback q).obj G)) :=
  (canonicalPairingModule (A := W.sheaf)
    (singleTensorMult (X := W.toRingedSpace)
      (𝟙 (((sheafTensor W.sheaf).obj ((Scheme.Modules.pullback p).obj F)).obj
        ((Scheme.Modules.pullback q).obj G))) 0 0 0 rfl) (m : ℤ) (n : ℤ)).hom
    ((hgroupModuleShiftIso (X := W.toRingedSpace) ((Scheme.Modules.pullback p).obj F) 0 m m
        (by simp)).hom a ⊗ₜ
      (hgroupModuleShiftIso (X := W.toRingedSpace) ((Scheme.Modules.pullback q).obj G) 0 n n
        (by simp)).hom b)

/-- **The cup product with `p^*θ` factors through the section `j` of `q`**: for `θ ∈ Hⁿ(X, F)`
and `ε, ε' ∈ Hⁿ(W, q^*G)` with `j^*ε = j^*ε'`, `p^*θ ∪ ε = p^*θ ∪ ε'`. -/
def CupFactorsThroughSection (p q : W ⟶ X) (j : X ⟶ W) (F G : X.Modules) (n : ℕ) : Prop :=
  ∀ (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ n F)
    (ε ε' : Hgroup (structureSheafRing W.toRingedSpace) ⊤ n ((Scheme.Modules.pullback q).obj G)),
    (unitPullback j _ n).hom ε = (unitPullback j _ n).hom ε' →
      pullbackCup p q F G n n ((unitPullback p F n).hom θ) ε =
        pullbackCup p q F G n n ((unitPullback p F n).hom θ) ε'

end General

/-! ### Classes of forms on `X ×_A X` -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **The cup product of [Stacks, Tag 0G8C] on `W = X ×_A X`** of a class of `Hᵠ(W, Ωᵖ_{W/A})`
with a class of `H^{0+c}(W, Ω^{0+c}_{W/A})`, both read through `hgroupModuleShiftIso`, the second
after the identification of the degree of the forms. -/
def cupOnProduct (p q c : ℕ)
    (a : Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ q
      (relativeDifferentialForms (prodStructure f) (p : ℤ)))
    (b : Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + c)
      (relativeDifferentialForms (prodStructure f) (((0 : ℕ) : ℤ) + (c : ℤ)))) :=
  (hodgeCupStructureSheaf (prodStructure f) p c q c).hom
    ((hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
      (relativeDifferentialForms (prodStructure f) (p : ℤ)) 0 q q (by simp)).hom a ⊗ₜ
    (hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
      (relativeDifferentialForms (prodStructure f) (c : ℤ)) 0 (0 + c) c (by push_cast; ring)).hom
      ((Hfunctor (pullback f f).ringCatSheaf ⊤ (0 + c)).map
        (eqToHom (congrArg (relativeDifferentialForms (prodStructure f)) (by push_cast; ring))) b))

/-- **`p₁^*` on classes of forms**, the pullback of [Stacks, Tag 01F9] along the canonical map
`Ωᵖ_{X/A} ⟶ p₁_*Ωᵖ_{W/A}`. -/
def fstPullback (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ q
        (relativeDifferentialForms (prodStructure f) (p : ℤ)) :=
  pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
    0 (q : ℤ) q (by simp) (formsBaseChangeHom (pullback.fst f f) f (prodStructure f) (𝟙 _)
      (fst_comp_eq_prodStructure f) (p : ℤ))

/-- **`p₂^*` on classes of forms.** -/
def sndPullback (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ q
        (relativeDifferentialForms (prodStructure f) (p : ℤ)) :=
  pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
    0 (q : ℤ) q (by simp) (formsBaseChangeHom (pullback.snd f f) f (prodStructure f) (𝟙 _)
      (snd_comp_eq_prodStructure f) (p : ℤ))

variable (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]

/-- **The Gysin class `η = γ_Δ(1) ∈ Hⁿ(W, Ωⁿ_{W/A})` of the diagonal.** -/
def diagonalClass :
    Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + (e + 1))
      (relativeDifferentialForms (prodStructure f) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) :=
  haveI := smooth_prodStructure f (e + 1)
  gysinUnitClass (pullback.diagonal f) (prodStructure f)
    (diagonal_koszul_and_conormalRank f (e + 1)).1 (diagonal_koszul_and_conormalRank f (e + 1)).2

variable (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ] [LocallyOfFinitePresentation σ]
  [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- **`p₁^*ξ`**, in the spelling of
`Stacks.DeRham.CohomologicalGysin.pullbackHgroup_sectionGysinClass_fst`. -/
def fstSectionClass :
    Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + (e + 1))
      (relativeDifferentialForms (prodStructure f) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.fst f f).toLRSHom.toShHom)
    (0 : ℤ) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (0 + (e + 1)) (by omega)
    (formsBaseChangeHom (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 _)
      (by rw [Category.comp_id]) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))).hom
    (sectionGysinClass f σ (e + 1))

/-- **`p₂^*ξ`**, in the spelling of
`Stacks.DeRham.CohomologicalGysin.pullbackHgroup_sectionGysinClass_snd`. -/
def sndSectionClass :
    Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (0 + (e + 1))
      (relativeDifferentialForms (prodStructure f) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ))) :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  (pullbackHgroup (CohomologyPullbackComparison.canonical (pullback.snd f f).toLRSHom.toShHom)
    (0 : ℤ) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (0 + (e + 1)) (by omega)
    (formsBaseChangeHom (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 _)
      (by rw [Category.comp_id, pullback.condition]) (((0 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)))).hom
    (sectionGysinClass f σ (e + 1))

/-- **The identity `(★)`** of the proof of [Stacks, Tag 0G8J] (its claim `θ₁ = θ₂ = θ`): for
`θ ∈ Hⁿ(X, Ω^{n-1}_{X/A})`, `p₁^*θ ∪ η = p₁^*θ ∪ p₂^*ξ + p₂^*θ ∪ p₁^*ξ` in
`H^{2n}(W, Ω^{2n-1}_{W/A})`. -/
def StarIdentity : Prop :=
  ∀ θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f (e : ℤ)),
    cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ) (diagonalClass f e) =
      cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ)
          (sndSectionClass f e σ) +
        cupOnProduct f e (e + 1) (e + 1) ((sndPullback f e (e + 1)).hom θ)
          (fstSectionClass f e σ)

/-- **Top-degree injectivity in cup form**: `x ↦ p₂^*x ∪ p₁^*ξ` is injective on
`Hⁿ(X, Ωⁿ_{X/A})`. -/
def CupTopInjective : Prop :=
  ∀ x : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)),
    cupOnProduct f (e + 1) (e + 1) (e + 1) ((sndPullback f (e + 1) (e + 1)).hom x)
        (fstSectionClass f e σ) = 0 → x = 0

/-- The two instances of `CupFactorsThroughSection` the identity `(★)` rests on typecheck. -/
example (hσ : σ ≫ f = 𝟙 _) : Prop :=
  CupFactorsThroughSection (pullback.fst f f) (pullback.snd f f) (sectionFst f σ hσ)
      (relativeDifferentialForms f (e : ℤ)) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
      (e + 1) ∧
    CupFactorsThroughSection (pullback.snd f f) (pullback.fst f f) (sectionSnd f σ hσ)
      (relativeDifferentialForms f (e : ℤ)) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
      (e + 1)

end Stacks.WeilDeRham

end
