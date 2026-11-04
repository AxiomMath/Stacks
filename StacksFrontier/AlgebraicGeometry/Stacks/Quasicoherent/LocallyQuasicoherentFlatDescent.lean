module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentSmoothDescent

/-!
# Local quasi-coherence along a jointly surjective flat, finitely presented family (Stacks 07AP)

Let `f j : 𝒵 j ⟶ 𝒳`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` which are
each flat (**Stacks 06PW**) and locally of finite presentation (**Stacks 06Q2**, part (1)) and
whose images cover the points of `𝒳`, that is `|𝒳| = ⋃ j, |f j|(|𝒵 j|)` for the points of
**Stacks 04XG**. Let `F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale`. **Stacks 07AP** says that if
every inverse image `f j^{-1} F` is locally quasi-coherent (**Stacks 06WJ**) then so is `F`.

The sheaf condition of **Stacks 06WJ** is a hypothesis on `F`, so what has to be proved is its
second clause: for every object `x` of `𝒳`, the restriction of `F` to the small étale site of the
scheme below `x` is quasi-coherent. This file proves the *fppf-local* half of that clause: by the
fppf-local factorisation of **Stacks 07AN**, every object `x` admits a family of arrows into `x`
lying over flat, locally finitely presented morphisms of schemes which cover the scheme below `x`,
at the sources of which the restriction of `F` is quasi-coherent.

Concluding requires fppf-locality of quasi-coherent small étale restrictions, isolated as the
predicate `AlgebraicGeometry.Stack.IsFppfLocalSmallEtaleQuasicoherence`. Its étale counterpart,
used for the smooth family of **Stacks 075Y**, is
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover`. The
source argues instead through the exact sequence `0 → F → a_*a^*F → b_*b^*F` of **Stacks 06XE**
and **Stacks 06XH**, **Stacks 075Z** and the two-out-of-three clause of **Stacks 06WM**.
**Stacks 07AP** itself, for a sheaf on `𝒳_fppf` with sections in the universe `u`, is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isFlat_isLfp_jointlySurjective`.

## Main definitions

* `AlgebraicGeometry.Stack.IsFppfLocalSmallEtaleQuasicoherence`: quasi-coherence of the small
  étale restriction of a fixed module may be checked after a jointly surjective family of flat,
  locally finitely presented arrows.

## Main results

* `AlgebraicGeometry.Stack.morphismProperty_map_left_of_isHomLift`: an arrow of a category fibred
  in groupoids lying over a morphism of the site has an underlying morphism of schemes with the
  same iso-invariant properties.
* `AlgebraicGeometry.Stack.exists_fppfCovering_isQuasicoherentOnSite_restrictModuleToSmallEtale`:
  **Stacks 07AP**, its fppf-local half.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isFppfLocal_of_isFlat_isLfp_jointlySurjective`
  gives the full conclusion of **Stacks 07AP**, granted fppf-locality of quasi-coherent small
  étale restrictions.

## Implementation notes

A 1-morphism of algebraic stacks is presented strictly, as in **Stacks 06WL**, through
`CategoryTheory.CatFiberedInGroupoids.homFunctor`. The sections of `F` live in an arbitrary
universe `m`, as do local quasi-coherence (**Stacks 06WJ**), the inverse image and the predicate
`AlgebraicGeometry.Stack.IsFppfLocalSmallEtaleQuasicoherence`.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 075Y](https://stacks.math.columbia.edu/tag/075Y)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 07AP](https://stacks.math.columbia.edu/tag/07AP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of schemes which is stable under composition and holds of every
isomorphism respects isomorphisms. -/
theorem respectsIso_of_isStableUnderComposition_of_isIso (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition]
    (hiso : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), IsIso g → P g) : P.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ g hg ↦ hiso g hg

/-- An arrow of a category fibred in groupoids lying over a morphism `k` of the site has an
underlying morphism of schemes with the same properties as that of `k`, for any property of
morphisms of schemes which respects isomorphisms. -/
theorem morphismProperty_map_left_of_isHomLift {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (P : MorphismProperty Scheme.{u}) (hP : P.RespectsIso)
    {U V : BigFppfOver B S hS} (k : V ⟶ U) (hk : P (B.inclusion.map k.left))
    {y x : 𝒳} (φ : y ⟶ x) (hφ : p.IsHomLift k φ) :
    P (B.inclusion.map (p.map φ).left) := by
  have := hP
  have := hφ
  have hfac := IsHomLift.fac' p k φ
  have hleft : (p.map φ).left =
      (eqToHom (IsHomLift.domain_eq p k φ)).left ≫ k.left ≫
        (eqToHom (IsHomLift.codomain_eq p k φ).symm).left := by
    rw [hfac]; rfl
  have hiso {a b : BigFppfOver B S hS} (e : a = b) :
      IsIso (B.inclusion.map (eqToHom e).left) := by
    change IsIso ((Over.forget (B.obj hS) ⋙ B.inclusion).map (eqToHom e))
    infer_instance
  have := hiso (IsHomLift.domain_eq p k φ)
  have := hiso (IsHomLift.codomain_eq p k φ).symm
  rwa [hleft, Functor.map_comp, Functor.map_comp, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]

/-- **Fppf-locality of quasi-coherent small étale restrictions.** For a presheaf of modules `F`
on a category fibred in groupoids which is a sheaf for the étale topology, this is the statement
that the second clause of **Stacks 06WJ** for `F` may be checked after a covering by flat,
locally finitely presented arrows: whenever arrows `φ i : y i ⟶ x` of `𝒳` lie over morphisms of
schemes which are flat, locally of finite presentation and jointly surjective onto the scheme
below `x`, and the restriction of `F` to the small étale site is quasi-coherent at every `y i`,
then it is quasi-coherent at `x`.

The same statement with "flat and locally of finite presentation" replaced by "étale" is
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover`, from
the locality of quasi-coherence on a site (**Stacks 03DN**). -/
noncomputable abbrev IsFppfLocalSmallEtaleQuasicoherence {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf) : Prop :=
  ∀ (x : 𝒳) {I : Type (u + 1)} (y : I → 𝒳) (φ : ∀ i, y i ⟶ x),
    (∀ i, Flat (B.inclusion.map (p.map (φ i)).left)) →
    (∀ i, LocallyOfFinitePresentation (B.inclusion.map (p.map (φ i)).left)) →
    (∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (φ i)).left)) →
    (∀ i, (⟨restrictModuleToSmallEtale B E h S hS p hp (y i) (etaleTopology B)
          (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp (y i) F hF⟩ :
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj (y i)).left.1
        (contains_base B E h S hS p (y i)))).IsQuasicoherentOnSite) →
    (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩ :
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).IsQuasicoherentOnSite

/-- **Stacks 07AP, its fppf-local half.** Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat, locally
finitely presented 1-morphisms of algebraic stacks over `S` with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, let
`F` be a sheaf of `𝒪_𝒳`-modules on `𝒳_étale` and suppose every inverse image `f j^{-1} F` is
locally quasi-coherent. Then every object `x` of `𝒳` admits a family of arrows `φ i : y i ⟶ x`
lying over flat, locally finitely presented and jointly surjective morphisms of schemes, at every
member of which the restriction of `F` to the small étale site is quasi-coherent. -/
@[stacks 07AP "the fppf-local half: every object acquires a jointly surjective family of flat, \
locally finitely presented arrows at whose sources the small étale restriction of the module is \
quasi-coherent, via the fppf-local factorisation of Stacks 07AN"]
theorem exists_fppfCovering_isQuasicoherentOnSite_restrictModuleToSmallEtale {J : Type v}
    {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, m} B S hS (f j)).obj F))
    (x : 𝒳.val.val.obj) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳.val.val.obj) (φ : ∀ i, y i ⟶ x),
      (∀ i, Flat (B.inclusion.map (𝒳.val.val.p.map (φ i)).left)) ∧
        (∀ i, LocallyOfFinitePresentation (B.inclusion.map (𝒳.val.val.p.map (φ i)).left)) ∧
          (∀ t : B.inclusion.obj (𝒳.val.val.p.obj x).left,
            ∃ i, t ∈ Set.range (B.inclusion.map (𝒳.val.val.p.map (φ i)).left)) ∧
            ∀ i, (⟨restrictModuleToSmallEtale B E h S hS 𝒳.val.val.p
                  𝒳.val.isFiberedInGroupoids (y i) (etaleTopology B)
                  (etaleTopology_le_topology B) F,
                restrictModuleToSmallEtale_isSheaf B E h S hS 𝒳.val.val.p
                  𝒳.val.isFiberedInGroupoids (y i) F hF⟩ :
              SheafOfModules.{m} (SmallEtale.structureSheaf E
                (𝒳.val.val.p.obj (y i)).left.1
                (contains_base B E h S hS 𝒳.val.val.p (y i)))).IsQuasicoherentOnSite := by
  classical
  obtain ⟨I, W, k, a, hkflat, hklfp, hkcov, hklift⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  choose zz αα hαα using hklift
  refine ⟨I, fun i ↦ (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj (zz i), αα,
    fun i ↦ ?_, fun i ↦ ?_, fun t ↦ ?_, fun i ↦ ?_⟩
  · exact morphismProperty_map_left_of_isHomLift B S hS 𝒳.val.val.p @Flat
      MorphismProperty.IsStableUnderBaseChange.respectsIso
      _ (hkflat i) (αα i) (hαα i)
  · exact morphismProperty_map_left_of_isHomLift B S hS 𝒳.val.val.p
      @LocallyOfFinitePresentation
      MorphismProperty.IsStableUnderBaseChange.respectsIso
      _ (hklfp i) (αα i) (hαα i)
  · obtain ⟨i, hi⟩ := hkcov t
    exact ⟨i, range_map_left_of_isHomLift B S hS 𝒳.val.val.p (αα i) (hαα i) hi⟩
  · exact isQuasicoherentOnSite_restrictModuleToSmallEtale_image.{u, u + 1, u, u + 1, u, m}
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor (f (a i)).hom)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f (a i)).hom)
      (isFibredOneMorphism_homFunctor_comp B S hS (f (a i)).hom) F hF (hlqc (a i)) (zz i)

/-- **The conclusion of Stacks 07AP, granted fppf-locality of quasi-coherent small étale
restrictions.** Let `f j : 𝒵 j ⟶ 𝒳` be a family of flat, locally finitely presented 1-morphisms
of algebraic stacks over `S` with `|𝒳| = ⋃ j, |f j|(|𝒵 j|)`, and let `F` be a sheaf of
`𝒪_𝒳`-modules on `𝒳_étale` every inverse image `f j^{-1} F` of which is locally quasi-coherent.
If `F` satisfies `AlgebraicGeometry.Stack.IsFppfLocalSmallEtaleQuasicoherence` then `F` is locally
quasi-coherent.

No `@[stacks]` attribute is recorded: the statement of **Stacks 07AP** is the conclusion without
that hypothesis, which for a sheaf on `𝒳_fppf` with sections in the universe `u` is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isFlat_isLfp_jointlySurjective`. -/
theorem isLocallyQuasicoherent_of_isFppfLocal_of_isFlat_isLfp_jointlySurjective {J : Type v}
    {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F.presheaf)
    (hlqc : ∀ j, IsLocallyQuasicoherent B E h S hS
      (CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒳.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS (f j).hom)
      ((stackModulePresheafPullback.{u, w, m} B S hS (f j)).obj F))
    (hloc : IsFppfLocalSmallEtaleQuasicoherence.{u, u + 1, u, m} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F hF) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F := by
  refine ⟨hF, fun x ↦ ?_⟩
  refine ⟨restrictModuleToSmallEtale_isSheaf B E h S hS _ _ x F hF, ?_⟩
  obtain ⟨I, y, φ, hφflat, hφlfp, hφcov, hφqc⟩ :=
    exists_fppfCovering_isQuasicoherentOnSite_restrictModuleToSmallEtale.{u, v, w, m}
      B E h S hS f hflat hlfp hjs F hF hlqc x
  exact hloc x y φ hφflat hφlfp hφcov hφqc

end AlgebraicGeometry.Stack

end
