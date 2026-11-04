module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredCechVanishingFlatAffine
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings

/-!
# Cohomology over an affine object of a module cartesian along flat morphisms of affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `ℱ` a sheaf of `𝒪_𝒳`-modules
on the associated fppf site, with module sections in the universe `u` of the schemes.  Suppose
that for every object `x` of `𝒳` lying over an affine scheme `X` and every `z ⟶ x` lying over a
flat morphism of affine schemes `Z ⟶ X`, the comparison `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)` is
bijective — which is what a locally quasi-coherent module with the flat base change property
satisfies.  Then

`Hⁿ(x, ℱ) = 0` for `n > 0` and every `x` lying over an affine scheme.

This is the vanishing the source obtains, in the proof of Stacks 08IY and of Stacks 075R, from
Stacks 075F, 0756 and 01XB.  The argument is Stacks 03F9: the finite fppf coverings by objects
lying over affine schemes are cofinal among the coverings of an object lying over an affine
scheme (`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le`), they and all their
iterated fibre products lie over affine schemes, and the Čech cohomology of `ℱ` vanishes on them
by Stacks 03FJ (`AlgebraicGeometry.FibredSite.isZero_cechCohomology_succ_of_tensorToSections`).
The cohomology of the underlying abelian sheaf is then compared with the right derived functors
of module-valued sections by
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv`.

## Main results

* `AlgebraicGeometry.FibredSite.isAffine_prop_piObj`: an iterated fibre product over `x` of
  objects lying over affine schemes `P` over the affine scheme below `x` (`P` flat or étale) lies
  over an affine scheme `P` over it.
* `AlgebraicGeometry.FibredSite.isZero_sheafCohomology_of_isAffine`: the vanishing of the
  cohomology of the underlying abelian sheaf.
* `AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine`: **the vanishing of
  the right derived functors of module-valued sections**.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite
  Stacks.Cohomology.ModuleDirectImageOnACover

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

include hp in
/-- **An iterated fibre product over `x` of a family of objects lying over affine schemes `P`
over the affine scheme below `x` lies over an affine scheme `P` over it.** -/
theorem isAffine_prop_piObj (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x))
    (E : PreZeroHypercover.{u} x) (haff : ∀ i, IsAffine (schemeOf B S hS p (E.X i)))
    (hflat : ∀ i, P ((p ⋙ BigFppfOver.toScheme B S hS).map (E.f i)))
    (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    letI : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
    letI : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsAffine (schemeOf B S hS p (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) ∧
      P ((sliceToSchemes B S hS p x).obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a))))).hom := by
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let : HasFiniteLimits (Over x) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let := preservesPullbacks_of_isFiberedInGroupoids B S hS p hp
  let v : 𝒳 ⥤ Scheme.{u} := p ⋙ BigFppfOver.toScheme B S hS
  let A : Fin (n + 1) → Over x := fun a ↦ Over.mk (E.f (i a))
  have : IsAffine (v.obj x) := hx
  let _ : PreservesLimit (Discrete.functor A) (Over.post (X := x) v) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost v E
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
  have haffhom : ∀ a, IsAffineHom ((Over.post (X := x) v).obj (A a)).hom := fun a ↦ by
    have : IsAffine ((Over.post (X := x) v).obj (A a)).left := haff (i a)
    exact isAffineHom_of_isAffine _
  have : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ haffhom
  have haffprod : IsAffine (∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a))).hom
  let e : (Over.post (X := x) v).obj (∏ᶜ A) ≅ ∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a)) :=
    PreservesProduct.iso (Over.post (X := x) v) A
  refine ⟨?_, ?_⟩
  · have e' : schemeOf B S hS p (∏ᶜ A).left ≅
        (∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a))).left :=
      (Over.forget (v.obj x)).mapIso e
    exact IsAffine.of_isIso e'.hom
  · have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    have h1 : P (e.hom.left ≫ (∏ᶜ (fun a ↦ (Over.post (X := x) v).obj (A a))).hom) :=
      P.comp_mem _ _ (P.of_isIso _)
        (prop_over_finiteProduct P _ fun a ↦ hflat (i a))
    rwa [Over.w e.hom] at h1

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The cartesian condition along flat morphisms of affines: the comparison
`Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)` is invertible at every object `z ⟶ x` of the slice at an
object `x` lying over an affine scheme, with `z` lying over an affine scheme flat over it. -/
def IsCartesianAlongFlatAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) : Prop :=
  ∀ (x : 𝒳), IsAffine (schemeOf B S hS p x) → ∀ Z : Over x, IsAffine (schemeOf B S hS p Z.left) →
    Flat ((sliceToSchemes B S hS p x).obj Z).hom →
      IsIso (tensorToSectionsApp B S hS p hp .fppf x F (op Z))

/-- The finite fppf coverings by objects lying over affine schemes, of objects lying over affine
schemes. -/
def affineFppfCoverings (x : 𝒳) :
    Set { E : PreZeroHypercover.{u} x //
      E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x } :=
  { E | IsAffine (schemeOf B S hS p x) ∧ Finite E.1.I₀ ∧
      (∀ i, IsAffine (schemeOf B S hS p (E.1.X i))) ∧
      Presieve.ofArrows (fun i => schemeOf B S hS p (E.1.X i))
        (fun i => (p ⋙ BigFppfOver.toScheme B S hS).map (E.1.f i)) ∈
      Scheme.fppfPrecoverage (schemeOf B S hS p x) }

omit [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The maps of a covering in `affineFppfCoverings` lie over flat morphisms of schemes. -/
private theorem flat_map_of_mem_affineFppfCoverings {x : 𝒳}
    {E : { E : PreZeroHypercover.{u} x //
      E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x }}
    (hE : E ∈ affineFppfCoverings B S hS p x) (i : E.1.I₀) :
    Flat ((p ⋙ BigFppfOver.toScheme B S hS).map (E.1.f i)) := by
  obtain ⟨-, -, -, hfppf⟩ := hE
  unfold Scheme.fppfPrecoverage at hfppf
  exact (((Scheme.ofArrows_mem_precoverage_iff _).1 hfppf).2 i).1

omit [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}] in
include hp in
/-- The finite fppf coverings by affine objects are cofinal among the coverings of an object
lying over an affine scheme. -/
theorem exists_affineFppfCoverings_le {x : 𝒳} (hx : IsAffine (schemeOf B S hS p x))
    (R : Sieve x) (hR : R ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    ∃ E : { E : PreZeroHypercover.{u} x //
        E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x },
      E ∈ affineFppfCoverings B S hS p x ∧ E.1.sieve₀ ≤ R := by
  obtain ⟨n, z, φ, haff, hmem, hcov, hfppf⟩ :=
    exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hR
  let E : PreZeroHypercover.{u} x := ⟨ULift (Fin n), fun i => z i.down, fun i => φ i.down⟩
  have hsieve : E.sieve₀ = Sieve.ofArrows z φ := by
    apply le_antisymm
    · rintro W g ⟨Y, a, b, ⟨i⟩, rfl⟩
      exact ⟨_, a, φ i.down, ⟨i.down⟩, rfl⟩
    · rintro W g ⟨Y, a, b, ⟨i⟩, rfl⟩
      exact ⟨_, a, E.f ⟨i⟩, Presieve.ofArrows.mk (ι := E.I₀) ⟨i⟩, rfl⟩
  refine ⟨⟨E, hsieve ▸ hcov⟩, ⟨hx, inferInstance, fun i => haff i.down,
    Scheme.mem_fppfPrecoverage_of_equiv Equiv.ulift hfppf⟩, hsieve.le.trans ?_⟩
  rintro W g ⟨Y, a, b, ⟨i⟩, rfl⟩
  exact R.downward_closed (hmem i) a

include hp in
/-- **The cohomology of the underlying abelian sheaf of a module cartesian along flat morphisms
of affines vanishes in positive degrees over every object lying over an affine scheme.** -/
theorem isZero_sheafCohomology_of_isAffine
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : IsCartesianAlongFlatAffines B S hS p hp F) {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x)) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf (ringStructureSheafCore B S hS p hp .fppf)).obj F)
      n x) := by
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let : ∀ y : 𝒳, HasFiniteLimits (Over y) :=
    fun y => hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : MorphismProperty.ContainsIdentities @Flat := ⟨fun X => inferInstanceAs (Flat (𝟙 X))⟩
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives.{u, u, u, v}
    (BigFppfOver.associatedTopology B S hS p .fppf) {y | IsAffine (schemeOf B S hS p y)}
    (affineFppfCoverings B S hS p) (fun E _ q i => inferInstance) ?_
    (fun y hy R hR => exists_affineFppfCoverings_le B S hS p hp hy R hR) _ ?_ x hx n hn
  · intro y E hE
    exact ⟨hE.1, hE.2.2.1, fun q i => (isAffine_prop_piObj B S hS p hp @Flat hE.1 E.1 hE.2.2.1
      (flat_map_of_mem_affineFppfCoverings B S hS p hE) q i).1⟩
  · intro y E hE q hq
    exact isZero_cechCohomology_succ_of_tensorToSections B S hS p hp @Flat hE.1 E.1 hE.2.1
      hE.2.2.1 hE.2.2.2 (flat_map_of_mem_affineFppfCoverings B S hS p hE) _
      (abelianPresheaf B S hS p hp .fppf F) (tensorToSections B S hS p hp .fppf y F)
      (hF y hE.1) q hq

variable [EnoughInjectives (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))]
  [HasExt.{max v u} (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [HasExt.{max v u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))]

include hp in
/-- **The right derived functors of sections over an object lying over an affine scheme vanish
in positive degrees on a module cartesian along flat morphisms of affines.** -/
theorem isZero_rightDerived_evaluation_of_isAffine
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : IsCartesianAlongFlatAffines B S hS p hp F) {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x)) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (ringStructureSheafCore B S hS p hp .fppf)
      (op x)).rightDerived n).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{v, u, u}
    (BigFppfOver.associatedTopology B S hS p .fppf) (ringStructureSheafCore B S hS p hp .fppf)
    x m F (isZero_sheafCohomology_of_isAffine B S hS p hp F hF hx (m + 1) hn)

end AlgebraicGeometry.FibredSite
