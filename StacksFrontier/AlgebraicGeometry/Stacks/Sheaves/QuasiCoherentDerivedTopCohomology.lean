module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology

/-!
# The top cohomology module of a quasi-coherent object (Stacks 0H0I)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. Stacks 0H0H defines the
triangulated category `QC(𝒳) = QC(𝒳_{affine}, O)` of quasi-coherent objects in the derived
category: the full subcategory of `D(𝒳_{affine}, O)` of the objects `K` for which every
canonical derived base-change map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism.

For such an object `M` the cohomology sheaves `H^i(M)` are in general *not* quasi-coherent. The
last nonvanishing one is: **Stacks 0H0I** says that if `b ∈ ℤ` is such that `H^i(M) = 0` for all
`i > b`, then `H^b(M)` is a quasi-coherent module on `(𝒳_{affine}, O)` in the sense of Stacks
0H0E.

As in the source, this is the instantiation at the associated affine site of the general
statement of Cohomology on Sites, Stacks 0GZQ, which is
`Stacks.ModulesOnACategory.TopCohomology.isQuasicoherentOnSite_topHomology`. The reason it holds
is that between an object of the derived category in degrees `≤ b` and one in degrees `≥ b`,
taking cohomology in degree `b` is bijective on morphisms. Evaluation at an object of
`𝒳_{affine}` is exact, so `RΓ(U, M)` is in degrees `≤ b` together with `M`; hence the universal
property of `RΓ(V, M) ⟶ RΓ(U, M)` for derived restriction of scalars, which is what membership
in `QC(𝒳)` says, descends to the universal property of `H^b(M)(V) ⟶ H^b(M)(U)` for restriction
of scalars — and on the chaotic site that property of a module is quasi-coherence.

## Main definitions

* `AlgebraicGeometry.Stack.affineChaoticRingSheaf`: the sheaf of rings `O` of Stacks 0H08, read
  as a sheaf on the associated affine site of Stacks 0H09 rather than as a presheaf. On the
  chaotic topology no sheaf condition is needed, so this repackages
  `AlgebraicGeometry.Stack.affineStructurePresheaf` and nothing more.
* `AlgebraicGeometry.Stack.affineHomologySheaf`: the cohomology module `H^i(M)` of an object of
  `D(𝒳_{affine}, O)`, read as a sheaf of `O`-modules.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_affineHomologySheaf`: **Stacks 0H0I.**
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_affineHomologySheaf_of_isQC`: the same for an
  object of `D(𝒳_{affine}, O)` carrying the quasi-coherence condition as a hypothesis, rather
  than for an object of the subcategory `QC(𝒳)`.
* `AlgebraicGeometry.Stack.affineChaoticRingSheaf_eq_ringedSite_chaotic_ringSheaf`: the ringed
  site on which the conclusion is read is the one Stacks 0H0E is about, namely the chaotic
  reading of `AlgebraicGeometry.Stack.AffineCategory.ringedSite`.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_affineHomologySheaf_iff`: the conclusion in the
  base-change form of condition (1) of Stacks 0H0E.

## Implementation notes

**Why `H^b(M)` is produced as a sheaf and not as an existential.** Stacks 0GZQ carries the sheaf
condition of `H^b(M)` as an existential in its conclusion, to avoid tying the universe of the
module to the universe of the ring. Here the topology of `𝒳_{affine}` is the chaotic one on the
nose — `AlgebraicGeometry.Stack.associatedAffineChaoticTopology` is reducibly `⊥` — so the
sheaf condition is supplied outright by `CategoryTheory.Presheaf.isSheaf_bot` and
`affineHomologySheaf` is an honest definition. The existential produced by 0GZQ is discharged
against it by proof irrelevance.

**The form in which the conclusion reads as Stacks 0H0E.** Condition (2) of Stacks 0H0E is
`SheafOfModules.IsQuasicoherentOnSite`, the notion of Modules on Sites, Stacks 03DL, and that is
what is concluded here. Condition (1) is the invertibility of the base-change maps
`F(x') ⊗_{O(x')} O(x) ⟶ F(x)`. The repository's form of their equivalence that is used below is
`Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow`, which phrases condition
(1) as the universal property of the restriction maps. That phrasing names no left adjoint of
restriction of scalars, so unlike
`AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_chaotic_iff_canonicalMap_isIso` —
the statement of Stacks 0H0E (1) ⇔ (2) in this development, which fixes the module universe to
be the ring universe — it holds at the module universe `max v w u t` that the cohomology of a
`D(O)`-object actually lives in, and no universe has to be identified with another.

**Universes.** These are those of Stacks 0H0H: the ambient big fppf site is at the scheme
universe `u`, the fibred category is `𝒳 : Type v` with `Category.{w} 𝒳`, and `D(O)` has
coefficient module universe `max v w u t` for a free parameter `t`. All four stay free.

## References

* [Stacks Project, Tag 0H0I](https://stacks.math.columbia.edu/tag/0H0I)
* [Stacks Project, Tag 0H0H](https://stacks.math.columbia.edu/tag/0H0H)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 0GZQ](https://stacks.math.columbia.edu/tag/0GZQ)
* [Stacks Project, Tag 0H09](https://stacks.math.columbia.edu/tag/0H09)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **The sheaf of rings `O` on the associated affine site.** The structure presheaf of Stacks
0H08 read as a sheaf on `𝒳_{affine}` with its chaotic topology of Stacks 0H09. Sheaves and
presheaves agree there, so the sheaf condition is `CategoryTheory.Presheaf.isSheaf_bot` and the
underlying presheaf is unchanged. -/
def affineChaoticRingSheaf : Sheaf (associatedAffineChaoticTopology B S hS p) RingCat.{u} :=
  ⟨affineStructurePresheaf B S hS p, Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of rings of `affineChaoticRingSheaf` is `affineStructurePresheaf`. -/
@[simp]
theorem affineChaoticRingSheaf_obj :
    (affineChaoticRingSheaf B S hS p).obj = affineStructurePresheaf B S hS p :=
  rfl

/-- The sheaf of rings above is the structure sheaf of the ringed site `(𝒳_{affine}, O)` that
Stacks 0H0E is about, read with the chaotic topology: for every topology `τ` and every proof
that `p` is fibred in groupoids, since by `affineStructurePresheaf_eq_restriction` the
underlying presheaf depends on neither. So the quasi-coherence concluded below is the one of
Stacks 0H0E. -/
theorem affineChaoticRingSheaf_eq_ringedSite_chaotic_ringSheaf (hp : p.IsFiberedInGroupoids)
    (τ : SiteKind) (J : GrothendieckTopology (BigAffineFppf B S hS))
    [(AffineCategory.inclusion B S hS p).IsContinuous (associatedAffineTopology B S hS p J)
      (BigFppfOver.associatedTopology B S hS p τ)] :
    (Stacks.SheafOfModules.Tensor.ringSheaf (AffineCategory.ringedSite B S hS p hp τ J).chaotic.O) =
      affineChaoticRingSheaf B S hS p :=
  rfl

/-- The cohomology module `H^i(M)` of an object of `D(𝒳_{affine}, O)`, read as a sheaf of
`O`-modules. On the chaotic site a presheaf of modules is already a sheaf, so this is the
cohomology presheaf of modules with the sheaf condition of
`CategoryTheory.Presheaf.isSheaf_bot` attached, and nothing is sheafified. -/
def affineHomologySheaf (M : DMod.{t} (affineStructurePresheaf B S hS p)) (i : ℤ) :
    SheafOfModules.{max v w u t} (affineChaoticRingSheaf B S hS p) :=
  ⟨(DerivedCategory.homologyFunctor
    (PresheafOfModules.{max v w u t} (affineStructurePresheaf B S hS p)) i).obj M,
    Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of modules of `affineHomologySheaf M i` is `H^i(M)`. -/
@[simp]
theorem affineHomologySheaf_val (M : DMod.{t} (affineStructurePresheaf B S hS p)) (i : ℤ) :
    (affineHomologySheaf.{u, v, w, t} B S hS p M i).val =
      (DerivedCategory.homologyFunctor
        (PresheafOfModules.{max v w u t} (affineStructurePresheaf B S hS p)) i).obj M :=
  rfl

/-- **Stacks 0H0I, for an object of `D(𝒳_{affine}, O)` satisfying the quasi-coherence
condition.** If `M` satisfies the condition of Stacks 0GYV defining `QC(𝒳)` and `b` is an
integer with `H^i(M) = 0` for all `i > b`, then `H^b(M)` is a quasi-coherent module on
`(𝒳_{affine}, O)`. -/
theorem isQuasicoherentOnSite_affineHomologySheaf_of_isQC
    (M : DMod.{t} (affineStructurePresheaf B S hS p))
    (hM : IsQuasiCoherentObject.{u, v, w, t} B S hS p M) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max v w u t} (affineStructurePresheaf B S hS p)) i).obj M)) :
    (affineHomologySheaf.{u, v, w, t} B S hS p M b).IsQuasicoherentOnSite := by
  obtain ⟨_, h⟩ :=
    Stacks.ModulesOnACategory.TopCohomology.isQuasicoherentOnSite_topHomology.{t, v, w, u}
      (R := affineChaoticRingSheaf B S hS p) rfl
      (affineBaseChangeData.{u, v, w, t} B S hS p) M hM b hvan
  exact h

/-- **Stacks 0H0I.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `M` be
an object of the triangulated category `QC(𝒳)` of Stacks 0H0H, and let `b ∈ ℤ` be such that
`H^i(M) = 0` for all `i > b`. Then `H^b(M)` is a quasi-coherent module on the ringed site
`(𝒳_{affine}, O)`, in the sense of Stacks 0H0E. -/
@[stacks 0H0I]
theorem isQuasicoherentOnSite_affineHomologySheaf
    (M : quasiCoherentDerived.{u, v, w, t} B S hS p) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max v w u t} (affineStructurePresheaf B S hS p)) i).obj M.obj)) :
    (affineHomologySheaf.{u, v, w, t} B S hS p M.obj b).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_affineHomologySheaf_of_isQC.{u, v, w, t} B S hS p M.obj M.property b hvan

/-- The quasi-coherence concluded by Stacks 0H0I, in the base-change form of condition (1) of
Stacks 0H0E: every restriction map `H^b(M)(V) ⟶ H^b(M)(U)` is universal among `O(V)`-linear
maps out of `H^b(M)(V)` into an `O(U)`-module, which is to say that
`H^b(M)(V) ⊗_{O(V)} O(U) ⟶ H^b(M)(U)` is an isomorphism. -/
theorem isQuasicoherentOnSite_affineHomologySheaf_iff
    (M : DMod.{t} (affineStructurePresheaf B S hS p)) (b : ℤ) :
    (affineHomologySheaf.{u, v, w, t} B S hS p M b).IsQuasicoherentOnSite ↔
      ∀ {U V : (AffineCategory B S hS p)ᵒᵖ} (a : V ⟶ U),
        (ModuleCat.restrictScalars ((affineStructurePresheaf B S hS p).map a).hom).IsUniversalArrow
          ((affineHomologySheaf.{u, v, w, t} B S hS p M b).val.map a) :=
  Stacks.ModulesOnACategory.isQuasicoherentOnSite_iff_isUniversalArrow.{v, w, u, t} rfl _

/-- **Stacks 0H0I in base-change form.** For `M` in `QC(𝒳)` with no cohomology above `b`, every
base-change map `H^b(M)(V) ⊗_{O(V)} O(U) ⟶ H^b(M)(U)` of the top cohomology module is an
isomorphism. -/
theorem isUniversalArrow_affineHomologySheaf_map
    (M : quasiCoherentDerived.{u, v, w, t} B S hS p) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max v w u t} (affineStructurePresheaf B S hS p)) i).obj M.obj))
    {U V : (AffineCategory B S hS p)ᵒᵖ} (a : V ⟶ U) :
    (ModuleCat.restrictScalars ((affineStructurePresheaf B S hS p).map a).hom).IsUniversalArrow
      ((affineHomologySheaf.{u, v, w, t} B S hS p M.obj b).val.map a) :=
  (isQuasicoherentOnSite_affineHomologySheaf_iff.{u, v, w, t} B S hS p M.obj b).mp
    (isQuasicoherentOnSite_affineHomologySheaf.{u, v, w, t} B S hS p M b hvan) a

end AlgebraicGeometry.Stack

end
