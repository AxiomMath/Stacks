module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapComponent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackOfGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionsComp

/-!
# The first case of Stacks 0ER5: a prime cycle not contained in the pulled-back divisor

In Situation 0EDT let `f : X' ⟶ X` be proper, let `(ℒ, s)` be an invertible sheaf on `X` with a
global section, `E = Z(s)` and `E' = Z(f^*s)`, and let `W' ⊆ X'` be an integral closed subspace
of δ-dimension `k + 1` with `W' ⊄ E'`. Write `W` for the closure of the image of `W'` and
`g : W' ⟶ W` for the component morphism of Stacks 0EEG. The source's first case of the proof of
Stacks 0ER5 is the identity of cycles on `W`

`g_* div_{ℒ'|_{W'}}(s'|_{W'}) = deg(W'/W) · div_{ℒ|_W}(s|_W)`,

for `ℒ' = f^*ℒ` and `s' = f^*s`, which is Stacks 0EQS for `g` once the restriction of the pulled
back pair to `W'` is identified with the pullback along `g` of the restriction of the pair to `W`:

* `(f^*ℒ)|_{W'} ≅ g^*(ℒ|_W)`, the two inverse images of `ℒ` along `W' ⟶ X` (Stacks 03LU),
  carries `(f^*s)|_{W'}` to `g^*(s|_W)`
  (`AlgebraicGeometry.Space.sectionsMap_modulePullbackCompCongrIso_hom_modulePullbackSections`);
* the meromorphic section of a pulled-back global section is the pullback of the meromorphic
  section (`AlgebraicGeometry.Space.pullbackMeromorphicSection_globalSectionMeromorphic`);
* the Weil divisor does not change along an isomorphism of invertible modules
  (`AlgebraicGeometry.Space.canonicalDivisorCycleAt_sectionsMap_iso`).

So the divisor of `(f^*s)|_{W'}` is the divisor of `g^*(s|_W)`
(`AlgebraicGeometry.Space.canonicalDivisorCycleAt_restrictedPullbackSection_eq`). Then:

* if `dim_δ(W) = k + 1` this is Stacks 0EQS for `g`;
* if `dim_δ(W) = k`, `g_*` of the divisor of a pulled-back section is zero
  (`Space.properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop`),
  and so is the right-hand side; this is the case the source passes over;
* if `dim_δ(W) < k` there are no `k`-cycles on `W`.

## Main results

* `AlgebraicGeometry.Space.canonicalDivisorCycleAt_restrictedPullbackSection_eq`
* `AlgebraicGeometry.Space.properPushforwardChernDefect_sectionGysinChernRule_eq_zero_of_not_le`

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes, as in
`StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Two spellings of the inclusion of a closed subspace -/

/-- The inclusion of a closed subspace, spelled through `AlgebraicGeometry.Space.closedSubspaceHom`
and through `AlgebraicGeometry.Space.closedSubspaceInclusion`, is one morphism. -/
theorem closedSubspaceHom_eq_closedSubspaceInclusion (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    closedSubspaceHom D.site D.base D.base_mem hX Y hY =
      closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hX⟩ ⟨Y, hY⟩ :=
  rfl

/-! ### Weil divisors of global sections along isomorphisms and equal pullbacks -/

section Transport

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)

/-- **The Weil divisor of a global section along an isomorphism of invertible modules.** For
`e : ℳ ≅ ℳ'`, `div_{ℳ'}(e(σ)) = div_ℳ(σ)`. -/
theorem canonicalDivisorCycleAt_globalSectionMeromorphic_sectionsMap_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M)
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ M') (e : M ≅ M') (σ : M.sections)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M σ))
    (hσ' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 M'
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M'
        (SheafOfModules.sectionsMap e.hom σ)))
    {k : ℤ} (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint M' hM'
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M'
          (SheafOfModules.sectionsMap e.hom σ)) hσ' hk =
      canonicalDivisorCycleAt D sY hY hint M hM
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 M σ) hσ hk :=
  (canonicalDivisorCycleAt_congr_section D hY hint M' hM' hσ'
      (isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem Y hY.1 e _ hσ) hk
      (sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic D.site D.base D.base_mem
        hY.1 e.hom σ).symm).trans
    (canonicalDivisorCycleAt_sectionsMap_iso D sY hY hint M M' hM hM' e _ hσ
      (isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem Y hY.1 e _ hσ) hk)

/-- **The Weil divisor of a pulled-back global section along equal morphisms.** -/
theorem canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_congr
    {Z : AlgebraicSpaces D.site D.base D.base_mem} {a b : (⟨Y, hY.1⟩ : AlgebraicSpaces _ _ _) ⟶ Z}
    (hab : a = b) (L : Modules.{u, u} D.site D.base D.base_mem Z.1 Z.2) (σ : L.sections)
    (hMa : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩
      ((modulePullback D.site D.base D.base_mem a).obj L))
    (hMb : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩
      ((modulePullback D.site D.base D.base_mem b).obj L))
    (ha : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem a L σ)))
    (hb : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem b L σ)))
    {k : ℤ} (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint _ hMa
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem a L σ)) ha hk =
      canonicalDivisorCycleAt D sY hY hint _ hMb
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem b L σ)) hb hk := by
  subst hab
  rfl

/-- Regularity of the meromorphic section of an iterated pullback of a global section passes to
the pullback along the composite. -/
private theorem isRegular_globalSectionMeromorphic_modulePullbackSections_comp
    {Z Z' : AlgebraicSpaces D.site D.base D.base_mem} (a : (⟨Y, hY.1⟩ : AlgebraicSpaces _ _ _) ⟶ Z)
    (b : Z ⟶ Z') (L : Modules.{u, u} D.site D.base D.base_mem Z'.1 Z'.2) (σ : L.sections)
    (h : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem a _
          (modulePullbackSections D.site D.base D.base_mem b L σ)))) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem (a ≫ b) L σ)) := by
  have h' := isRegularMeromorphicSection_sectionsMap_of_iso D.site D.base D.base_mem Y hY.1
    ((modulePullbackCompIso D.site D.base D.base_mem a b).app L) _ h
  convert h' using 2
  rw [meromorphicSectionSheafMapIso_hom]
  refine ((sectionsMap_meromorphicSectionSheafMap_globalSectionMeromorphic D.site D.base
    D.base_mem hY.1 _ _).trans ?_).symm
  exact congrArg (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _)
    (sectionsMap_modulePullbackCompIso_modulePullbackSections D.site D.base D.base_mem a b L σ)

/-- **The Weil divisor of an iterated pullback of a global section is that of the pullback
along the composite**, the two modules being identified by Stacks 03LU. -/
theorem canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp
    {Z Z' : AlgebraicSpaces D.site D.base D.base_mem} (a : (⟨Y, hY.1⟩ : AlgebraicSpaces _ _ _) ⟶ Z)
    (b : Z ⟶ Z') (L : Modules.{u, u} D.site D.base D.base_mem Z'.1 Z'.2) (σ : L.sections)
    (hM : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩
      ((modulePullback D.site D.base D.base_mem a).obj
        ((modulePullback D.site D.base D.base_mem b).obj L)))
    (hM' : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩
      ((modulePullback D.site D.base D.base_mem (a ≫ b)).obj L))
    (h1 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem a _
          (modulePullbackSections D.site D.base D.base_mem b L σ))))
    (h2 : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (modulePullbackSections D.site D.base D.base_mem (a ≫ b) L σ)))
    {k : ℤ} (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalDivisorCycleAt D sY hY hint _ hM
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem a _
            (modulePullbackSections D.site D.base D.base_mem b L σ))) h1 hk =
      canonicalDivisorCycleAt D sY hY hint _ hM'
        (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
          (modulePullbackSections D.site D.base D.base_mem (a ≫ b) L σ)) h2 hk := by
  have hs := sectionsMap_modulePullbackCompIso_modulePullbackSections D.site D.base D.base_mem
    a b L σ
  have h2' : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _
        (SheafOfModules.sectionsMap ((modulePullbackCompIso D.site D.base D.base_mem a b).app L).hom
          (modulePullbackSections D.site D.base D.base_mem a _
            (modulePullbackSections D.site D.base D.base_mem b L σ)))) := by
    rwa [Iso.app_hom, hs]
  exact (canonicalDivisorCycleAt_globalSectionMeromorphic_sectionsMap_iso D hY hint _ _ hM hM'
    ((modulePullbackCompIso D.site D.base D.base_mem a b).app L) _ h1 h2' hk).symm.trans
    (canonicalDivisorCycleAt_congr_section D hY hint _ hM' h2' h2 hk
      (congrArg (globalSectionMeromorphic D.site D.base D.base_mem hY.1 _) hs))

end Transport

/-! ### The divisor of the restricted pulled-back section -/

section NonContained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (g : W'.subspace.toFunctor ⟶ (chernImage D hp' hp f W').subspace.toFunctor)
    (hg : g ≫ (chernImage D hp' hp f W').subspace.ι = W'.subspace.ι ≫ f.hom)

/-- Regularity of the meromorphic section of a pulled-back global section only depends on the
morphism. -/
theorem isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_congr
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    {Z : AlgebraicSpaces D.site D.base D.base_mem} {a b : (⟨Y, hY⟩ : AlgebraicSpaces _ _ _) ⟶ Z}
    (hab : a = b) (M : Modules.{u, u} D.site D.base D.base_mem Z.1 Z.2) (σ : M.sections)
    (h : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem a M σ))) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY _
      (globalSectionMeromorphic D.site D.base D.base_mem hY _
        (modulePullbackSections D.site D.base D.base_mem b M σ)) := by
  subst hab
  exact h

include hL hg in
/-- **The divisor of `(f^*s)|_{W'}` is the divisor of `g^*(s|_W)`.** For `W' ⊆ X'` with closure
`W` of its image and component morphism `g : W' ⟶ W`, the Weil divisor on `W'` of the
restriction of the pulled-back global section `f^*s` to `W'` is the Weil divisor of the pullback
along `g` of the restriction of `s` to `W`: both are inverse images of `s` along `W' ⟶ X`, by
the two routes of the commutative square (Stacks 03LU). -/
theorem canonicalDivisorCycleAt_restrictedPullbackSection_eq {k : ℤ}
    (hk : deltaDimensionClosed D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hM₁ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (integralClosedSubspaceRestrict D p' hp' (pullbackSheaf D p hp p' hp' f L) W'))
    (hM₂ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      ((modulePullback D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)).obj
        (chernImageModule D hp' hp f L W')))
    (h₁ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem W'.isClosedSubspace.1 _
        (integralClosedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s) W')))
    (h₂ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
        (chernImageModule D hp' hp f L W')
        (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg)
        (globalSectionMeromorphic D.site D.base D.base_mem
          (chernImage D hp' hp f W').isClosedSubspace.1 _
          (integralClosedSubspaceRestrictSection D p hp L s (chernImage D hp' hp f W'))))) :
    canonicalDivisorCycleAt D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
        W'.isIntegralSpace _ hM₁
        (globalSectionMeromorphic D.site D.base D.base_mem W'.isClosedSubspace.1 _
          (integralClosedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
            (pullbackGlobalSection D p hp p' hp' f L s) W'))
        h₁ hk =
      canonicalDivisorCycleAt D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
        W'.isIntegralSpace _ hM₂
        (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
          (chernImageModule D hp' hp f L W')
          (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg)
          (globalSectionMeromorphic D.site D.base D.base_mem
            (chernImage D hp' hp f W').isClosedSubspace.1 _
            (integralClosedSubspaceRestrictSection D p hp L s (chernImage D hp' hp f W'))))
        h₂ hk := by
  have hsq :
      (closedSubspaceHom D.site D.base D.base_mem hp'.1 W'.subspace W'.isClosedSubspace) ≫ f =
        (chernComponentHom D hp' hp f W' g) ≫
          (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
            (chernImage D hp' hp f W').isClosedSubspace) := ObjectProperty.hom_ext _ hg.symm
  have hLm : IsInvertibleModule (B := D.site) (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      L := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have R₃ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem W'.isClosedSubspace.1 _
        (modulePullbackSections D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g) _
          (modulePullbackSections D.site D.base D.base_mem
            (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
              (chernImage D hp' hp f W').isClosedSubspace) L s))) := by
    rw [← pullbackMeromorphicSection_globalSectionMeromorphic D.site D.base D.base_mem
      (chernComponentHom D hp' hp f W' g) _
      (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg)]
    convert h₂ using 3
  have R₂ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem W'.isClosedSubspace.1 _
        (modulePullbackSections D.site D.base D.base_mem ((chernComponentHom D hp' hp f W' g) ≫
          (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
            (chernImage D hp' hp f W').isClosedSubspace)) L s)) := by
    convert isRegular_globalSectionMeromorphic_modulePullbackSections_comp D
      (isGood_integralClosedSubspace D p' hp' W') (chernComponentHom D hp' hp f W' g)
      (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
        (chernImage D hp' hp f W').isClosedSubspace) L s (by convert R₃ using 3) using 3
  have R₁ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (globalSectionMeromorphic D.site D.base D.base_mem W'.isClosedSubspace.1 _
        (modulePullbackSections D.site D.base D.base_mem
          (closedSubspaceHom D.site D.base D.base_mem hp'.1 W'.subspace W'.isClosedSubspace ≫ f)
          L s)) :=
    isRegularMeromorphicSection_globalSectionMeromorphic_modulePullbackSections_congr D
      W'.isClosedSubspace.1 hsq.symm L s R₂
  have hI₁ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      ((modulePullback D.site D.base D.base_mem
        (closedSubspaceHom D.site D.base D.base_mem hp'.1 W'.subspace W'.isClosedSubspace ≫ f)).obj
          L) :=
    modulePullbackInvertible (W := ⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩)
      (V := ⟨X, hp.1⟩)
      (closedSubspaceHom D.site D.base D.base_mem hp'.1 W'.subspace W'.isClosedSubspace ≫ f) L hLm
  have hI₂ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      ((modulePullback D.site D.base D.base_mem ((chernComponentHom D hp' hp f W' g) ≫
        (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
          (chernImage D hp' hp f W').isClosedSubspace))).obj L) :=
    modulePullbackInvertible (W := ⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩)
      (V := ⟨X, hp.1⟩) ((chernComponentHom D hp' hp f W' g) ≫
        (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
          (chernImage D hp' hp f W').isClosedSubspace)) L hLm
  have e₁ := canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp D
    (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace
    (closedSubspaceHom D.site D.base D.base_mem hp'.1 W'.subspace W'.isClosedSubspace) f L s hM₁ hI₁
    (by convert h₁ using 3) (by convert R₁ using 3) hk
  have e₂ := canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_congr D
    (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace hsq L s hI₁ hI₂
    (by convert R₁ using 3) (by convert R₂ using 3) hk
  have e₃ := canonicalDivisorCycleAt_globalSectionMeromorphic_modulePullbackSections_comp D
    (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace
    (chernComponentHom D hp' hp f W' g)
    (closedSubspaceHom D.site D.base D.base_mem hp.1 (chernImage D hp' hp f W').subspace
      (chernImage D hp' hp f W').isClosedSubspace) L s hM₂ hI₂
    (by convert R₃ using 3) (by convert R₂ using 3) hk
  have e₄ := canonicalDivisorCycleAt_congr_section D (isGood_integralClosedSubspace D p' hp' W')
    W'.isIntegralSpace _ hM₂ (by convert R₃ using 3) (by convert h₂ using 3) hk
    (pullbackMeromorphicSection_globalSectionMeromorphic D.site D.base D.base_mem
      (chernComponentHom D hp' hp f W' g) _
      (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) _).symm
  exact e₁.trans (e₂.trans (e₃.symm.trans e₄))

end NonContained

/-! ### The first case -/

section FirstCase

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (hfbase : f.hom ≫ p = p') (hf : IsProper D.site D.base D.base_mem f.hom)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)

/-- The restriction `s|_W` of the global section to the closure `W` of the image of `W'`, read
as a meromorphic section of `ℒ|_W`; it is regular when `W ⊄ Z(s)`. -/
abbrev chernImageGlobalSection (W' : IntegralClosedSubspace D.site D.base D.base_mem X') :
    MeromorphicSection.{u, u} D.site D.base D.base_mem (chernImage D hp' hp f W').subspace.toFunctor
      (chernImage D hp' hp f W').isClosedSubspace.1 (chernImageModule D hp' hp f L W') :=
  globalSectionMeromorphic D.site D.base D.base_mem (chernImage D hp' hp f W').isClosedSubspace.1 _
    (integralClosedSubspaceRestrictSection D p hp L s (chernImage D hp' hp f W'))

/-- **Stacks 0EQS for the component morphism `g : W' ⟶ W`**, in the form the two cases of
Stacks 0ER5 consume: for a regular meromorphic section `t` of `ℒ|_W` and `dim_δ(W) = k + 1`,
`g_* div_{g^*(ℒ|_W)}(g^*t) = deg(W'/W) · div_{ℒ|_W}(t)`, the degree being that of Stacks 0EP1
of `f` at `W'`. This is
`AlgebraicGeometry.Space.properCyclePushforward_canonicalDivisorCycleAt_pullback` together with
the reading of the degree on the component morphism. -/
theorem subspaceProperCyclePushforward_canonicalDivisorCycleAt_chernComponentHom
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (g : W'.subspace.toFunctor ⟶ (chernImage D hp' hp f W').subspace.toFunctor)
    (hg : g ≫ (chernImage D hp' hp f W').subspace.ι = W'.subspace.ι ≫ f.hom)
    (hM : IsInvertibleModule (B := D.site)
      (⟨(chernImage D hp' hp f W').subspace.toFunctor,
        (chernImage D hp' hp f W').isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (chernImageModule D hp' hp f L W'))
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem
      (chernImage D hp' hp f W').subspace.toFunctor (chernImage D hp' hp f W').isClosedSubspace.1
      (chernImageModule D hp' hp f L W'))
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _ _ _ t)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
        (chernImageModule D hp' hp f L W')
        (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) t))
    (hk : deltaDimensionClosed D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hk' : deltaDimensionClosed D ((chernImage D hp' hp f W').subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hW' : deltaDimension D p' W' = k + 1)
    (heq : deltaDimension D p (chernImage D hp' hp f W') = k + 1) :
    subspaceProperCyclePushforward D p' hp' p hp hfbase hf W' _ g hg k
        (canonicalDivisorCycleAt D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
          W'.isIntegralSpace _ (modulePullbackInvertible (chernComponentHom D hp' hp f W' g) _ hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
            (chernImageModule D hp' hp f L W')
            (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) t) hσ hk) =
      properCycleDegree D p' hp' p hp f.hom W' •
        canonicalDivisorCycleAt D ((chernImage D hp' hp f W').subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp _) (chernImage D hp' hp f W').isIntegralSpace _
          hM t ht hk' := by
  rw [properCycleDegree_eq_functionFieldDegreeAtGenericPoint D hp' hp f W' g hg hfbase hf hW' heq]
  exact properCyclePushforward_canonicalDivisorCycleAt_pullback D (W'.subspace.ι ≫ p')
    (isGood_integralClosedSubspace D p' hp' W') ((chernImage D hp' hp f W').subspace.ι ≫ p)
    (isGood_integralClosedSubspace D p hp _) W'.isIntegralSpace
    (chernImage D hp' hp f W').isIntegralSpace _ hM _ _
    (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hp'.1 hp.1 f.hom hf W'
      _ g hg)
    (IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base D.base_mem hp.1
      (D.isDecentSpace_of_isGood p hp) f.hom W' _ hg) _ ht _ hk'

include hL in
/-- **The source's first case of Stacks 0ER5.** Let `W' ⊆ X'` be an integral closed subspace of
δ-dimension `k + 1` not contained in `E' = Z(f^*s)`, with closure `W` of its image and component
morphism `g : W' ⟶ W`. Then the defect of the projection formula at `W'`, for the Gysin component
rules of `(f^*ℒ, f^*s)` and of `(ℒ, s)`, vanishes as a cycle: `g_*` of the divisor of
`(f^*s)|_{W'} = g^*(s|_W)` is `deg(W'/W)` times the divisor of `s|_W` (Stacks 0EQS for `g`), or
zero when the dimension drops. -/
theorem properPushforwardChernDefect_sectionGysinChernRule_eq_zero_of_not_le
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW' : deltaDimension D p' W' = k + 1)
    (hW'E' : ¬ W'.subspace ≤ (pullbackSectionVanishingLocus D p hp p' hp' f L s).1) :
    properPushforwardChernDefect D hp' hp hfbase hf k
        (sectionGysinChernRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)
          (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) k)
        (sectionGysinChernRule D p hp L s hL k) W' = 0 := by
  classical
  obtain ⟨g, hg⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f.hom W'
  have hE'eq : (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 =
      (vanishingLocus D p hp L s).1.preimage f.hom :=
    (congrArg Subtype.val (pullbackDivisor_eq_vanishingLocus D p hp p' hp' f L s hL)).symm
  have hpt : subspacePointSet D.site D.base D.base_mem X'
        (pullbackSectionVanishingLocus D p hp p' hp' f L s).1 =
      pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1 := by
    rw [hE'eq]
    exact subspacePointSet_preimage D.site D.base D.base_mem f.hom _
  have hWE := not_le_closureImage_of_not_le D p hp p' hp' f.hom _ _ hpt W' hW'E'
  rw [properPushforwardChernDefect_eq D hp' hp hfbase hf k _ _ W' g hg]
  refine (congrArg _ ?_).trans (map_zero _)
  rw [chernComponentCycleOrZero_of_deltaDimension_eq D p' k _ hW', sectionGysinChernRule,
    restrictedSectionChernRule, dite_eq_right hW'E']
  have hLm : IsInvertibleModule (B := D.site) (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      L := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hk : deltaDimensionClosed D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p' hp' W', hW']
  have hMW : IsInvertibleModule (B := D.site)
      (⟨(chernImage D hp' hp f W').subspace.toFunctor,
        (chernImage D hp' hp f W').isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (chernImageModule D hp' hp f L W') :=
    modulePullbackInvertible (W := ⟨(chernImage D hp' hp f W').subspace.toFunctor,
        (chernImage D hp' hp f W').isClosedSubspace.1⟩) (V := ⟨X, hp.1⟩) _ L hLm
  have hs0 : integralClosedSubspaceRestrictSection D p hp L s (chernImage D hp' hp f W') ≠ 0 :=
    closedSubspaceRestrictSection_ne_zero D p hp L s hL
      ⟨(chernImage D hp' hp f W').subspace, (chernImage D hp' hp f W').isClosedSubspace⟩ hWE
  have ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem _ _ _
      (chernImageGlobalSection D p hp p' hp' f L s W') :=
    isRegularMeromorphicSection_of_ne_zero_of_isGood D _
      (isGood_integralClosedSubspace D p hp (chernImage D hp' hp f W'))
      (chernImage D hp' hp f W').isIntegralSpace _ hMW
      (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem _ _ hMW hs0)
  have hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W'.subspace.toFunctor
      W'.isClosedSubspace.1 _
      (pullbackMeromorphicSection D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)
        (chernImageModule D hp' hp f L W')
        (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg)
        (chernImageGlobalSection D p hp p' hp' f L s W')) :=
    isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
      (chernComponentHom D hp' hp f W' g)
      (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) _
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hMW) _ ht
  have hL'm : IsInvertibleModule (B := D.site)
      (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) (pullbackSheaf D p hp p' hp' f L) :=
    modulePullbackInvertible (W := ⟨X', hp'.1⟩) (V := ⟨X, hp.1⟩) f L hLm
  have hM₁ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (integralClosedSubspaceRestrict D p' hp' (pullbackSheaf D p hp p' hp' f L) W') :=
    modulePullbackInvertible (W := ⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩)
      (V := ⟨X', hp'.1⟩) _ _ hL'm
  have hM₂ : IsInvertibleModule (B := D.site)
      (⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      ((modulePullback D.site D.base D.base_mem (chernComponentHom D hp' hp f W' g)).obj
        (chernImageModule D hp' hp f L W')) :=
    modulePullbackInvertible (W := ⟨W'.subspace.toFunctor, W'.isClosedSubspace.1⟩)
      (V := ⟨(chernImage D hp' hp f W').subspace.toFunctor,
        (chernImage D hp' hp f W').isClosedSubspace.1⟩) _ _ hMW
  have hs0' : integralClosedSubspaceRestrictSection D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s) W' ≠ 0 :=
    closedSubspaceRestrictSection_ne_zero D p' hp' _ _
      (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) ⟨W'.subspace, W'.isClosedSubspace⟩
      hW'E'
  have h₁ := isRegularMeromorphicSection_of_ne_zero_of_isGood D (W'.subspace.ι ≫ p')
    (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace _ hM₁
    (globalSectionMeromorphic_ne_zero D.site D.base D.base_mem _ _ hM₁ hs0')
  have hT1 := canonicalDivisorCycleAt_restrictedPullbackSection_eq D p hp p' hp' f L s hL W' g hg
    hk hM₁ hM₂ h₁ hσ
  simp only [integralClosedSubspaceRestrict, integralClosedSubspaceRestrictSection,
    closedSubspaceHom] at hT1
  simp only [closedSubspaceRestrictSheaf, closedSubspaceRestrictSection, closedSubspaceInclusion,
    closedSubspaceToSpace]
  rw [hT1]
  have hle : deltaDimension D p (chernImage D hp' hp f W') ≤ k + 1 := by
    rw [← hW']
    exact IntegralClosedSubspace.deltaDimension_closureImage_le D p' p hp' hp f.hom hfbase W'
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- the equal-dimensional case: Stacks 0EQS for `g`
    have hk' : deltaDimensionClosed D ((chernImage D hp' hp f W').subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp _) Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) := by
      rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp _, heq]
    have h0 := subspaceProperCyclePushforward_canonicalDivisorCycleAt_chernComponentHom D p hp p'
      hp' f hfbase hf L k W' g hg hMW _ ht hσ hk hk' hW' heq
    simp only [chernImageGlobalSection, integralClosedSubspaceRestrictSection,
      closedSubspaceHom] at h0
    rw [h0, chernComponentCycleOrZero_of_deltaDimension_eq D p k _ heq, sectionGysinChernRule,
      restrictedSectionChernRule, dite_eq_right hWE, sub_eq_zero]
    simp only [closedSubspaceRestrictSheaf, closedSubspaceRestrictSection, closedSubspaceInclusion,
      closedSubspaceToSpace, chernImageModule, integralClosedSubspaceRestrict, closedSubspaceHom]
  rcases eq_or_lt_of_le (show deltaDimension D p (chernImage D hp' hp f W') ≤ k by omega) with
    heq | hlt'
  · -- the dimension-drop case
    have hgB : (chernComponentHom D hp' hp f W' g).hom ≫ (chernImage D hp' hp f W').subspace.ι ≫ p =
        W'.subspace.ι ≫ p' := by
      show g ≫ _ ≫ p = _
      rw [← Category.assoc, hg, Category.assoc, hfbase]
    have hσ0 := properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop
      D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W') W'.isIntegralSpace
      ((chernImage D hp' hp f W').subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp _)
      (chernImage D hp' hp f W').isIntegralSpace (chernComponentHom D hp' hp f W' g) hgB
      (IntegralClosedSubspace.isProper_of_comp_ι_eq D.site D.base D.base_mem hp'.1 hp.1 f.hom hf W'
        _ g hg).2.1.2
      (pullbacksMeromorphicSections_chernComponentHom D hp' hp f W' g hg) k hk
      ((IntegralClosedSubspace.deltaValue_comp_ι_genericPoint D p hp _
        (isGood_integralClosedSubspace D p hp _)).trans heq)
      _ hMW _ ht hσ
    simp only [chernImageGlobalSection, integralClosedSubspaceRestrictSection,
      closedSubspaceHom] at hσ0
    rw [chernComponentCycleOrZero_of_deltaDimension_ne D p k _
      (fun h => by have := h.symm.trans heq; omega), smul_zero, sub_zero]
    exact hσ0
  · -- no `k`-cycles on `W`
    exact cycleGroup_eq_zero_of_deltaDimension_lt D p hp _ k hlt' _

end FirstCase

end AlgebraicGeometry.Space

end
