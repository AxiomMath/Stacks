module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningCubeComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.CocontinuousLocalizedMate

/-!
# Inverse images and comparisons of direct images of small étale modules along equal data

For morphisms of algebraic spaces given up to equality of their sources and targets, the inverse
image (in the four-field reading `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`) of
heterogeneously equal maps of modules are heterogeneously equal
(`AlgebraicGeometry.Space.toRingedToposModulesHom_pullbackModules_map_heq`), and so are the
components of the comparisons `AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq` of direct
images at heterogeneously equal modules
(`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq_hom_app_heq`). These let two spellings of the
same map, whose spaces are written differently, be compared one piece at a time.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Inverse images of heterogeneously equal maps along equal morphisms**: for `p : V ⟶ T` and
`p' : V ⟶ T'` heterogeneously equal along `T = T'`, and maps `l`, `l'` of modules heterogeneously
equal, the inverse images `p^*l` and `p'^*l'` (four-field reading) are heterogeneously equal. -/
theorem toRingedToposModulesHom_pullbackModules_map_heq {V T T' : AlgebraicSpaces B S hS}
    (e : T = T') {p : V ⟶ T} {p' : V ⟶ T'} (ep : p ≍ p')
    {N₁ N₂ : spaceModules T} {N₁' N₂' : spaceModules T'} (e₁ : N₁ ≍ N₁') (e₂ : N₂ ≍ N₂')
    {l : N₁ ⟶ N₂} {l' : N₁' ⟶ N₂'} (el : l ≍ l') :
    (smallEtaleRingedToposHom B S hS p).toRingedToposModulesHom.pullbackModules.map l ≍
      (smallEtaleRingedToposHom B S hS p').toRingedToposModulesHom.pullbackModules.map l' := by
  subst e
  cases ep
  cases e₁
  cases e₂
  cases el
  rfl

/-- **Components of the comparison of direct images along equal data**: the components of
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq f g k hk` and of
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq f' g' k' hk'` at heterogeneously equal
modules are heterogeneously equal when the morphisms are (along equal spaces). -/
theorem modulePushforwardCompIsoOfEq_hom_app_heq {X Y Z X' Y' Z' : AlgebraicSpaces B S hS}
    (eX : X = X') (eY : Y = Y') (eZ : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} {hk : f ≫ g = k}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {k' : X' ⟶ Z'} {hk' : f' ≫ g' = k'}
    (ef : f ≍ f') (eg : g ≍ g') (ek : k ≍ k') {M : spaceModules X} {M' : spaceModules X'}
    (eM : M ≍ M') :
    (modulePushforwardCompIsoOfEq f g k hk).hom.app M ≍
      (modulePushforwardCompIsoOfEq f' g' k' hk').hom.app M' := by
  subst eX eY eZ
  cases ef
  cases eg
  cases ek
  cases eM
  obtain rfl : hk = hk' := Subsingleton.elim _ _
  rfl

end AlgebraicGeometry.Space

end
