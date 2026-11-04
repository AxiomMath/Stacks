module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The étale descent datum carried by the sheaf of relative differentials

Let `p : U ⟶ Y` be a morphism of schemes and let `s, t : R ⟶ U` be étale morphisms with
`s ≫ p = t ≫ p`: the situation of an étale presentation `U ⟶ X` of an algebraic space over a
scheme `Y`, with `R = U ×_X U`.  Because `s` and `t` are étale the canonical maps
`s^*Ω_{U/Y} ⟶ Ω_{R/Y}` and `t^*Ω_{U/Y} ⟶ Ω_{R/Y}` of Stacks 01UV are isomorphisms, so they
compose to an isomorphism

```
α : s^*Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t^*Ω_{U/Y},
```

and `α` satisfies the cocycle condition on any scheme carrying three compatible legs to `U`.
It is therefore a descent datum, and when the quotient is a scheme it is the canonical descent
datum of `Ω_{X/Y}` pulled back along the presentation: for `π : U ⟶ X` over `Y` with
`s ≫ π = t ≫ π`, the canonical map `π^*Ω_{X/Y} ⟶ Ω_{U/Y}` carries the canonical descent
isomorphism of `π^*Ω_{X/Y}` to `α`.  For a quotient which is an algebraic space the same
identification is
`AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso_canonicalComparison` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsDescent.lean`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackFactorIso`: the canonical isomorphism
  `g^*h^*M ≅ a^*M` attached to a factorization `g ≫ h = a`.
* `AlgebraicGeometry.Scheme.Modules.pullbackDescentIso`: the canonical descent isomorphism
  `s^*π^*M ≅ t^*π^*M` of a module pulled back along `π`, when `s ≫ π = t ≫ π`.
* `AlgebraicGeometry.Scheme.Hom.triangleDifferentialsMap` and
  `AlgebraicGeometry.Scheme.Hom.triangleDifferentialsIso`: the canonical map
  `h^*Ω_{U/Y} ⟶ Ω_{W/Y}` of a triangle over `Y`, and that map for étale `h`, where it is an
  isomorphism.
* `AlgebraicGeometry.Scheme.Hom.differentialsDescentIso`: **the descent isomorphism `α`.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.eq_differentialsDescentIso_hom`: `α` is the unique morphism
  whose composite with `t^*Ω_{U/Y} ⟶ Ω_{R/Y}` is `s^*Ω_{U/Y} ⟶ Ω_{R/Y}`.
* `AlgebraicGeometry.Scheme.Hom.pullback_differentialsDescentIso`: pulling `α` back along a
  morphism into `R` and normalizing by the canonical factorization isomorphisms gives the
  descent isomorphism of the two resulting legs.
* `AlgebraicGeometry.Scheme.Hom.differentialsDescentIso_trans`: the descent isomorphisms of
  three étale legs over `U` compose.
* `AlgebraicGeometry.Scheme.Hom.differentialsDescentIso_cocycle`: **`α` satisfies the cocycle
  condition.**
* `AlgebraicGeometry.Scheme.Hom.differentialsDescentIso_pullbackDescentIso`: for a quotient
  `π : U ⟶ X` which is a scheme, `α` is the canonical descent datum of `π^*Ω_{X/Y}`.

## Implementation notes

Everything is deduced from the uniqueness half of Stacks 01UV: the predicate
`AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap` mentions only the three morphisms of
a square, it is closed under composition, and it has at most one solution, so each identity
below is obtained by exhibiting both of its sides as a map of relative differentials for the
same triangle.  In particular the cocycle condition needs no computation with local sections:
the pullback of `α` along a leg is again a descent isomorphism of the same shape, and descent
isomorphisms over a fixed base compose because they are built from one family of comparison
isomorphisms to `Ω_{R/Y}`.

## References

* [Stacks Project, Tag 04CW](https://stacks.math.columbia.edu/tag/04CW)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical isomorphism `g^*h^*M ≅ a^*M` attached to a factorization `g ≫ h = a`: the
composition comparison of module pullback followed by the comparison of two equal
morphisms. -/
noncomputable def pullbackFactorIso {T R U : Scheme.{u}} (g : T ⟶ R) (h : R ⟶ U) {a : T ⟶ U}
    (hga : g ≫ h = a) (M : U.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M) ≅
      (Scheme.Modules.pullback a).obj M :=
  (Scheme.Modules.pullbackComp g h).app M ≪≫ (Scheme.Modules.pullbackCongr hga).app M

/-- The canonical descent isomorphism `s^*π^*M ≅ t^*π^*M` of a module pulled back along
`π : U ⟶ X`, for two morphisms `s, t : R ⟶ U` that agree after `π`. -/
noncomputable def pullbackDescentIso {R U X : Scheme.{u}} (π : U ⟶ X) {s t : R ⟶ U}
    (hπ : s ≫ π = t ≫ π) (M : X.Modules) :
    (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback π).obj M) ≅
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback π).obj M) :=
  pullbackFactorIso s π rfl M ≪≫ (Scheme.Modules.pullbackCongr hπ).app M ≪≫
    (pullbackFactorIso t π rfl M).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {Y U R : Scheme.{u}}

/-- The canonical map `h^*Ω_{U/Y} ⟶ Ω_{W/Y}` of a triangle `h : W ⟶ U` over `Y`: the map of
Stacks 01UV attached to the commutative square whose base morphism is the identity of `Y`. -/
noncomputable def triangleDifferentialsMap {W : Scheme.{u}} (h : W ⟶ U) (p : U ⟶ Y)
    (r : W ⟶ Y) (hr : h ≫ p = r) :
    (Scheme.Modules.pullback h).obj (relativeDifferentials p) ⟶ relativeDifferentials r :=
  relativeDifferentialsMap h p r (𝟙 Y) (by rw [hr, Category.comp_id])

/-- The canonical map of a triangle over `Y` is compatible with the universal derivations. -/
theorem isRelativeDifferentialsMap_triangleDifferentialsMap {W : Scheme.{u}} (h : W ⟶ U)
    (p : U ⟶ Y) (r : W ⟶ Y) (hr : h ≫ p = r) :
    IsRelativeDifferentialsMap h p r (triangleDifferentialsMap h p r hr) :=
  isRelativeDifferentialsMap_relativeDifferentialsMap h p r (𝟙 Y) _

/-- **The canonical map of a triangle over `Y` whose upper edge is étale is an isomorphism**:
this is Stacks 04BX for the square whose base morphism is the identity. -/
instance isIso_triangleDifferentialsMap {W : Scheme.{u}} (h : W ⟶ U) (p : U ⟶ Y) (r : W ⟶ Y)
    (hr : h ≫ p = r) [Etale h] : IsIso (triangleDifferentialsMap h p r hr) :=
  isIso_relativeDifferentialsMap_of_etale h p r (𝟙 Y) _

/-- The canonical isomorphism `h^*Ω_{U/Y} ≅ Ω_{W/Y}` of a triangle over `Y` whose upper edge
`h : W ⟶ U` is étale. -/
noncomputable def triangleDifferentialsIso {W : Scheme.{u}} (h : W ⟶ U) (p : U ⟶ Y)
    (r : W ⟶ Y) (hr : h ≫ p = r) [Etale h] :
    (Scheme.Modules.pullback h).obj (relativeDifferentials p) ≅ relativeDifferentials r :=
  asIso (triangleDifferentialsMap h p r hr)

/-- The forward map of `triangleDifferentialsIso` is `triangleDifferentialsMap`. -/
@[simp]
theorem triangleDifferentialsIso_hom {W : Scheme.{u}} (h : W ⟶ U) (p : U ⟶ Y) (r : W ⟶ Y)
    (hr : h ≫ p = r) [Etale h] :
    (triangleDifferentialsIso h p r hr).hom = triangleDifferentialsMap h p r hr :=
  rfl

/-- The inverse of `triangleDifferentialsIso` is the inverse of `triangleDifferentialsMap`. -/
@[simp]
theorem triangleDifferentialsIso_inv {W : Scheme.{u}} (h : W ⟶ U) (p : U ⟶ Y) (r : W ⟶ Y)
    (hr : h ≫ p = r) [Etale h] :
    (triangleDifferentialsIso h p r hr).inv = inv (triangleDifferentialsMap h p r hr) :=
  rfl

/-- The descent isomorphism `α : s^*Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t^*Ω_{U/Y}` attached to two étale
morphisms `s, t : R ⟶ U` of schemes over `Y` inducing the same morphism to `Y`. Both comparison
maps are isomorphisms because `s` and `t` are étale. -/
@[stacks 04CW "the descent isomorphism `α : s^*Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t^*Ω_{U/Y}`"]
noncomputable def differentialsDescentIso (p : U ⟶ Y) (s t : R ⟶ U) (q : R ⟶ Y)
    (hs : s ≫ p = q) (ht : t ≫ p = q) [Etale s] [Etale t] :
    (Scheme.Modules.pullback s).obj (relativeDifferentials p) ≅
      (Scheme.Modules.pullback t).obj (relativeDifferentials p) :=
  triangleDifferentialsIso s p q hs ≪≫ (triangleDifferentialsIso t p q ht).symm

/-- The defining property of the descent isomorphism: composed with the comparison map of `t`
it is the comparison map of `s`. -/
@[simp]
theorem differentialsDescentIso_hom_comp (p : U ⟶ Y) (s t : R ⟶ U) (q : R ⟶ Y)
    (hs : s ≫ p = q) (ht : t ≫ p = q) [Etale s] [Etale t] :
    (differentialsDescentIso p s t q hs ht).hom ≫ triangleDifferentialsMap t p q ht =
      triangleDifferentialsMap s p q hs := by
  simp [differentialsDescentIso]

/-- **The descent isomorphism is the unique morphism `s^*Ω_{U/Y} ⟶ t^*Ω_{U/Y}` compatible with
the comparison maps to `Ω_{R/Y}`.** -/
theorem eq_differentialsDescentIso_hom (p : U ⟶ Y) (s t : R ⟶ U) (q : R ⟶ Y)
    (hs : s ≫ p = q) (ht : t ≫ p = q) [Etale s] [Etale t]
    {φ : (Scheme.Modules.pullback s).obj (relativeDifferentials p) ⟶
      (Scheme.Modules.pullback t).obj (relativeDifferentials p)}
    (hφ : φ ≫ triangleDifferentialsMap t p q ht = triangleDifferentialsMap s p q hs) :
    φ = (differentialsDescentIso p s t q hs ht).hom := by
  rw [← Iso.cancel_iso_hom_right _ _ (triangleDifferentialsIso t p q ht),
    triangleDifferentialsIso_hom, hφ, differentialsDescentIso_hom_comp]

/-- The descent isomorphism of an étale morphism with itself is the identity. -/
@[simp]
theorem differentialsDescentIso_self (p : U ⟶ Y) (s : R ⟶ U) (q : R ⟶ Y) (hs : s ≫ p = q)
    [Etale s] : differentialsDescentIso p s s q hs hs = Iso.refl _ := by
  ext
  simp [differentialsDescentIso]

/-- **The descent isomorphisms of three étale legs over `U` compose.**  All three are built from
the comparison isomorphisms to `Ω_{R/Y}`, so the middle one cancels. -/
theorem differentialsDescentIso_trans (p : U ⟶ Y) (a₀ a₁ a₂ : R ⟶ U) (q : R ⟶ Y)
    (h₀ : a₀ ≫ p = q) (h₁ : a₁ ≫ p = q) (h₂ : a₂ ≫ p = q)
    [Etale a₀] [Etale a₁] [Etale a₂] :
    differentialsDescentIso p a₀ a₁ q h₀ h₁ ≪≫ differentialsDescentIso p a₁ a₂ q h₁ h₂ =
      differentialsDescentIso p a₀ a₂ q h₀ h₂ := by
  ext
  simp [differentialsDescentIso]

/-- **Precomposing a triangle over `Y` with a further morphism does not change its canonical
map**, once the pullback is normalized by the canonical factorization isomorphism: the
composite of the canonical maps of `u : R ⟶ U` and of `g : T ⟶ R` is the canonical map of
`g ≫ u`. -/
theorem pullbackFactorIso_inv_comp_triangleDifferentialsMap {T : Scheme.{u}} (p : U ⟶ Y)
    (u : R ⟶ U) (q : R ⟶ Y) (hu : u ≫ p = q) (g : T ⟶ R) {c : T ⟶ U} (r : T ⟶ Y)
    (hgu : g ≫ u = c) (hc : c ≫ p = r) (hr : g ≫ q = r) :
    (Scheme.Modules.pullbackFactorIso g u hgu (relativeDifferentials p)).inv ≫
        (Scheme.Modules.pullback g).map (triangleDifferentialsMap u p q hu) ≫
          triangleDifferentialsMap g q r hr =
      triangleDifferentialsMap c p r hc := by
  rw [Scheme.Modules.pullbackFactorIso]
  simp only [Iso.trans_inv, Iso.app_inv, Category.assoc]
  exact (((isRelativeDifferentialsMap_triangleDifferentialsMap u p q hu).comp
    (isRelativeDifferentialsMap_triangleDifferentialsMap g q r hr)).congr_left
      hgu).eq_relativeDifferentialsMap (𝟙 Y) (by rw [hc, Category.comp_id])

/-- **The pullback of the descent isomorphism along a morphism into `R` is the descent
isomorphism of the two resulting legs.**  The legs `a = g ≫ s` and `b = g ≫ t` are required to
be étale, and the normalization is by the canonical factorization isomorphisms
`g^*s^*Ω_{U/Y} ≅ a^*Ω_{U/Y}` and `g^*t^*Ω_{U/Y} ≅ b^*Ω_{U/Y}`. -/
theorem pullback_differentialsDescentIso {T : Scheme.{u}} (p : U ⟶ Y) (s t : R ⟶ U)
    (q : R ⟶ Y) (hs : s ≫ p = q) (ht : t ≫ p = q) [Etale s] [Etale t]
    (g : T ⟶ R) {a b : T ⟶ U} (r : T ⟶ Y) [Etale a] [Etale b]
    (hga : g ≫ s = a) (hgb : g ≫ t = b) (ha : a ≫ p = r) (hb : b ≫ p = r) :
    (Scheme.Modules.pullbackFactorIso g s hga (relativeDifferentials p)).inv ≫
        (Scheme.Modules.pullback g).map (differentialsDescentIso p s t q hs ht).hom ≫
          (Scheme.Modules.pullbackFactorIso g t hgb (relativeDifferentials p)).hom =
      (differentialsDescentIso p a b r ha hb).hom := by
  have hr : g ≫ q = r := by rw [← hs, ← Category.assoc, hga, ha]
  have hFb : (Scheme.Modules.pullbackFactorIso g t hgb (relativeDifferentials p)).hom ≫
      triangleDifferentialsMap b p r hb =
      (Scheme.Modules.pullback g).map (triangleDifferentialsMap t p q ht) ≫
        triangleDifferentialsMap g q r hr := by
    rw [← pullbackFactorIso_inv_comp_triangleDifferentialsMap p t q ht g r hgb hb hr,
      Iso.hom_inv_id_assoc]
  refine eq_differentialsDescentIso_hom p a b r ha hb ?_
  rw [Category.assoc, Category.assoc, hFb, ← Category.assoc
      ((Scheme.Modules.pullback g).map (differentialsDescentIso p s t q hs ht).hom),
    ← Functor.map_comp, differentialsDescentIso_hom_comp]
  exact pullbackFactorIso_inv_comp_triangleDifferentialsMap p s q hs g r hga ha hr

/-- **Stacks 04CW**, the cocycle condition.  Let `T` carry three étale legs `a₀, a₁, a₂ : T ⟶ U`
over `Y` and three morphisms `g₀₁, g₁₂, g₀₂ : T ⟶ R` realizing the pairs `(a₀, a₁)`, `(a₁, a₂)`
and `(a₀, a₂)` through `(s, t)`.  Then the pullback of `α` along `g₀₂` is the composite of its
pullbacks along `g₀₁` and `g₁₂`, each normalized by the canonical factorization isomorphisms.
So `α` is a descent datum. -/
@[stacks 04CW "the cocycle condition satisfied by `α`"]
theorem differentialsDescentIso_cocycle {T : Scheme.{u}} (p : U ⟶ Y) (s t : R ⟶ U) (q : R ⟶ Y)
    (hs : s ≫ p = q) (ht : t ≫ p = q) [Etale s] [Etale t]
    (g₀₁ g₁₂ g₀₂ : T ⟶ R) {a₀ a₁ a₂ : T ⟶ U} (r : T ⟶ Y) [Etale a₀] [Etale a₁] [Etale a₂]
    (h₀₁s : g₀₁ ≫ s = a₀) (h₀₁t : g₀₁ ≫ t = a₁) (h₁₂s : g₁₂ ≫ s = a₁)
    (h₁₂t : g₁₂ ≫ t = a₂) (h₀₂s : g₀₂ ≫ s = a₀) (h₀₂t : g₀₂ ≫ t = a₂)
    (h₀ : a₀ ≫ p = r) (h₁ : a₁ ≫ p = r) (h₂ : a₂ ≫ p = r) :
    (Scheme.Modules.pullbackFactorIso g₀₂ s h₀₂s (relativeDifferentials p)).inv ≫
        (Scheme.Modules.pullback g₀₂).map (differentialsDescentIso p s t q hs ht).hom ≫
          (Scheme.Modules.pullbackFactorIso g₀₂ t h₀₂t (relativeDifferentials p)).hom =
      ((Scheme.Modules.pullbackFactorIso g₀₁ s h₀₁s (relativeDifferentials p)).inv ≫
          (Scheme.Modules.pullback g₀₁).map (differentialsDescentIso p s t q hs ht).hom ≫
            (Scheme.Modules.pullbackFactorIso g₀₁ t h₀₁t (relativeDifferentials p)).hom) ≫
        ((Scheme.Modules.pullbackFactorIso g₁₂ s h₁₂s (relativeDifferentials p)).inv ≫
          (Scheme.Modules.pullback g₁₂).map (differentialsDescentIso p s t q hs ht).hom ≫
            (Scheme.Modules.pullbackFactorIso g₁₂ t h₁₂t (relativeDifferentials p)).hom) := by
  rw [pullback_differentialsDescentIso p s t q hs ht g₀₂ r h₀₂s h₀₂t h₀ h₂,
    pullback_differentialsDescentIso p s t q hs ht g₀₁ r h₀₁s h₀₁t h₀ h₁,
    pullback_differentialsDescentIso p s t q hs ht g₁₂ r h₁₂s h₁₂t h₁ h₂,
    ← differentialsDescentIso_trans p a₀ a₁ a₂ r h₀ h₁ h₂]
  rfl

/-- **For a quotient which is a scheme, `α` is the canonical descent datum of `π^*Ω_{X/Y}`.**
For `π : U ⟶ X` over `Y` with `s ≫ π = t ≫ π`, the canonical map `π^*Ω_{X/Y} ⟶ Ω_{U/Y}` of
Stacks 01UV carries the canonical descent isomorphism of `π^*Ω_{X/Y}` to `α`; when `π` is étale
that map is an isomorphism, so the module `α` descends to is `Ω_{X/Y}`.  The same identification
for a quotient which is an algebraic space is
`AlgebraicGeometry.Space.sheafOfDifferentialsDescentIso_canonicalComparison` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsDescent.lean`; here the comparison map
is constructed rather than hypothesized, so no input beyond the square is needed. -/
@[stacks 04CW "for a quotient which is a scheme, `α` agrees with the canonical descent datum \
of `π^*Ω_{X/Y}`"]
theorem differentialsDescentIso_pullbackDescentIso {X : Scheme.{u}} (pX : X ⟶ Y) (π : U ⟶ X)
    (p : U ⟶ Y) (hp : π ≫ pX = p) (s t : R ⟶ U) (q : R ⟶ Y) (hs : s ≫ p = q)
    (ht : t ≫ p = q) [Etale s] [Etale t] (hπ : s ≫ π = t ≫ π) :
    (Scheme.Modules.pullbackDescentIso π hπ (relativeDifferentials pX)).hom ≫
        (Scheme.Modules.pullback t).map (triangleDifferentialsMap π pX p hp) =
      (Scheme.Modules.pullback s).map (triangleDifferentialsMap π pX p hp) ≫
        (differentialsDescentIso p s t q hs ht).hom := by
  have hsπ : (s ≫ π) ≫ pX = q := by rw [Category.assoc, hp, hs]
  have htπ : (t ≫ π) ≫ pX = q := by rw [Category.assoc, hp, ht]
  have hcongr := ((isRelativeDifferentialsMap_triangleDifferentialsMap (s ≫ π) pX q
      hsπ).congr_left hπ).eq_relativeDifferentialsMap (𝟙 Y) (by rw [htπ, Category.comp_id])
  have hcongr' : (Scheme.Modules.pullbackCongr hπ).hom.app (relativeDifferentials pX) ≫
      triangleDifferentialsMap (t ≫ π) pX q htπ =
      triangleDifferentialsMap (s ≫ π) pX q hsπ := by
    rw [triangleDifferentialsMap, ← hcongr]
    simp
  rw [← Iso.cancel_iso_hom_right _ _ (triangleDifferentialsIso t p q ht),
    triangleDifferentialsIso_hom]
  simp only [Category.assoc, differentialsDescentIso_hom_comp,
    Scheme.Modules.pullbackDescentIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [pullbackFactorIso_inv_comp_triangleDifferentialsMap pX π p hp t q rfl htπ ht, hcongr',
    ← pullbackFactorIso_inv_comp_triangleDifferentialsMap pX π p hp s q rfl hsπ hs,
    Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.Hom

end
