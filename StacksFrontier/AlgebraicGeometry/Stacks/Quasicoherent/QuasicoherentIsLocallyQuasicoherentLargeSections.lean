module

public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransportFreeModuleUniverse
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcohLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherent

/-!
# Quasi-coherent modules are locally quasi-coherent at large module universes

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherent` proves
clause (a) of the forward direction of **Stacks 06WK** — a quasi-coherent module on
`(𝒳_{fppf}, 𝒪_𝒳)` (Stacks 06WG) is locally quasi-coherent (Stacks 06WJ) — with the module sections
in the universe `u` of the schemes. This file proves it with the sections in any universe
`max (u + 1) v w m`, which for an algebraic stack is any universe from `u + 1` on; that is the
universe at which the higher direct images and the coherator of the source's Chapter 104 live.
Nothing is assumed.

The proof is the one at universe `u`, each step replaced by its large-universe form:

1. the restriction to `𝒳_{affine, fppf}` is quasi-coherent
   (`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`, module-universe generic) and
   therefore cartesian over every arrow
   (`AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite_large`);
2. for every object `x` over `U` the restriction `x^*𝓕|_{U_{étale}}` is cartesian between affine
   objects, by the transport of the base-change comparison along the index functor of Stacks 06W1
   (`bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_freeModuleUniverse` in
   `Stacks.PresheafOfModules`);
3. hence quasi-coherent on `U_{étale}`, by Descent, Proposition 03DX (2) at the large universe,
   `SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite_freeModuleUniverse`:
  **clause (a) of the forward direction of Stacks 06WK at module universe `max (u + 1) v w m`.**
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite_succ`: the same for an
  algebraic stack at module universe `u + 1`; it applies verbatim to an object of
  `AlgebraicGeometry.Stack.fppfModulesUnivLE.{u, w, u + 1}`.
* `AlgebraicGeometry.Stack.forallQuasicoherentIsLocallyQuasicoherent_freeModuleUniverse`:
  `AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` at module universe
  `max (u + 1) v w m`, which covers the universe `max (u + 1) w m` at which
  `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_forallIsLocallyQuasicoherent`
  consumes it whenever `v ≤ max (u + 1) w m`.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
-/

@[expose] public section

open CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

open AffineCategory in
/-- **A quasi-coherent module on `𝒳_{fppf}` is cartesian on `𝒳_{affine}`, at module universe
`max (u + 1) v w m`.** For every arrow of the affine subcategory the base-change comparison of the
restriction of the module is an isomorphism. -/
theorem isIso_restrictionBaseChange_affine_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) {y y' : AffineCategory B S hS p} (f : y ⟶ y') :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := affineStructureCommPresheaf B S hS p)
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj M.val)
      f.op) := by
  have := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have := isCocontinuous_inclusion_siteKind B S hS p hp .fppf
  have : ∀ X : AffineCategory B S hS p,
      (Over.post (X := X) (AffineCategory.inclusion B S hS p)).IsContinuous
      ((associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf)).over X)
      ((BigFppfOver.associatedTopology B S hS p .fppf).over
        ((AffineCategory.inclusion B S hS p).obj X)) :=
    fun X =>
      have := Stacks.Sites.overPost_isDenseSubsite
        (J := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
        (K := BigFppfOver.associatedTopology B S hS p .fppf) (AffineCategory.inclusion B S hS p) X
      inferInstance
  have hres := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := BigFppfOver.associatedTopology B S hS p .fppf)
    (K := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (AffineCategory.inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf) M hM
  exact isIso_restrictionBaseChange_of_isQuasicoherentOnSite_large.{u, v, w, max (u + 1) v w m}
    B S hS p _ rfl hp .fppf _ _ hres f.op

/-- **The restriction of Stacks 06WJ is cartesian over a morphism `g` of the small étale site
exactly when the module is cartesian over the image of `g` under the index functor**, at module
universe `max (u + 1) v w m`. -/
theorem bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_freeModuleUniverse
    (G : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (x : 𝒳) {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (g : T ⟶ T') :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u,
        max (u + 1) v w m}
        (R := SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) G) g.op) ↔
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u,
        max (u + 1) v w m}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        G ((etaleIndex B E h S hS p hp x).map g).op) :=
  open Stacks.PresheafOfModules in
  bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_freeModuleUniverse.{
    v, w, u + 1, u, u, max (u + 1) v w m} (etaleIndex B E h S hS p hp x)
    (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj
    (SmallEtale.commStructurePresheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
    (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom
    (fun Z => ((localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).app Z).isIso_hom) G g.op

/-- **Clause (a) of the forward direction of Stacks 06WK, at module universe
`max (u + 1) v w m`.** A quasi-coherent module on the ringed site `(𝒳_{fppf}, 𝒪_𝒳)` is locally
quasi-coherent: it is a sheaf for the inherited étale topology, and for every object `x` of `𝒳`
lying over `U` its restriction `x^*𝓕|_{U_{étale}}` is quasi-coherent on the small étale site of
`U`. -/
theorem isLocallyQuasicoherent_of_isQuasicoherentOnSite_freeModuleUniverse
    (M : SheafOfModules.{max (u + 1) v w m}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherent B E h S hS p hp M.val := by
  have hsh : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) M.val.presheaf :=
    M.isSheaf.of_le (associatedTopology_etale_le_fppf B S hS p)
  refine ⟨hsh, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x M.val hsh, ?_⟩⟩
  refine SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse.{
    max v w m} B E h _ _ _ ?_
  intro T T' g hT hT'
  refine (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_freeModuleUniverse.{u, v,
    w, m} B E h S hS p hp M.val x g).2 ?_
  let yT : AffineCategory B S hS p :=
    ⟨(etaleIndex B E h S hS p hp x).obj T, isAffine_etaleIndex_obj B E h S hS p hp x T hT⟩
  let yT' : AffineCategory B S hS p :=
    ⟨(etaleIndex B E h S hS p hp x).obj T', isAffine_etaleIndex_obj B E h S hS p hp x T' hT'⟩
  let φ : yT ⟶ yT' := ObjectProperty.homMk ((etaleIndex B E h S hS p hp x).map g)
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_restrictionBaseChange_affine_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m}
      B S hS p hp M hM φ)

/-- **`AlgebraicGeometry.Stack.ForallQuasicoherentIsLocallyQuasicoherent` at module universe
`max (u + 1) v w m`, with no hypothesis.** -/
theorem forallQuasicoherentIsLocallyQuasicoherent_freeModuleUniverse :
    ForallQuasicoherentIsLocallyQuasicoherent.{u, v, w, max (u + 1) v w m} B S hS p hp :=
  fun M => isLocallyQuasicoherent_of_isQuasicoherentOnSite_freeModuleUniverse.{u, v, w, m} B
    (associatedBigEtaleSite B) rfl S hS p hp M.obj M.property

/-- **Clause (a) of the forward direction of Stacks 06WK for an algebraic stack, at module
universe `u + 1`.** A quasi-coherent module on the fppf site of `𝒳` with sections in `Type (u + 1)`
is locally quasi-coherent. -/
theorem isLocallyQuasicoherent_of_isQuasicoherentOnSite_succ (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (M : SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.val :=
  isLocallyQuasicoherent_of_isQuasicoherentOnSite_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M hM

end AlgebraicGeometry.Stack
