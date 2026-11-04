module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalBase
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal automorphisms of a scheme are its derivations

Let `k` be a field and `X` a scheme over `k`. The infinitesimal-automorphism clause of
[Stacks Project, Tag 0DY9] is the four-fold chain

`Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`,

and this file proves the identifications it is made of, for an arbitrary point of the
deformation category over an object of `𝒞_Λ` carrying a dual-number coordinate. The statement
itself, at the trivial deformation `X ×_{Spec k} Spec k[ε]`, is
`Deformation.Examples.infinitesimalAutomorphismGroupTrivialDeformationChain`.

The first identification is an **isomorphism of groups**. `Inf(𝓓_X)` is the automorphisms of the
trivial deformation `X' = X ×_{Spec k} Spec k[ε]` that are the identity modulo `ε`, a group under
composition, and the content is that composition of such self-maps corresponds to *addition* of
derivations. That is `Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`
read through the bijection of
`Stacks.Thickenings.derivationActionGlobalEquivOfBase`: the simply transitive action of
[Stacks Project, Tag 04FJ] gives additivity in the acting derivation, which is a statement about
iterating the action and not about composing two self-maps, so it does not by itself make the
induced bijection a homomorphism.

The remaining two identifications are additive. `Ext⁰` out of the naive cotangent complex is the
`Hom` out of its degree `0` cohomology sheaf, which is `Ω_{X/k}` by [Stacks Project, Tag 0D0J]
(`AlgebraicGeometry.Scheme.naiveCotangentExtZeroAddEquiv`); and `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is
`Der_k(𝒪_X, 𝒪_X)` by corepresentability of relative derivations
(`Deformation.Examples.schemeMorphismDerivationsAddEquiv`).

## Main definitions

* `Deformation.Examples.structureSheafModules`: `𝒪_X` as a sheaf of modules over itself.
* `Deformation.Examples.schemeMorphismPushforwardStructureSheaf_id`: the pushforward of 𝒪_X
  along the identity of `X` is 𝒪_X, which is why the fourth term of the chain is
  `Der_k(𝒪_X, 𝒪_X)`.
* `Deformation.Examples.schemeMorphismLiftHomAddEquiv`: the global homomorphisms
  `f^*Ω_{Y/k} ⟶ 𝒞_{X/X'}` are `Der_k(𝒪_Y, f_*𝒪_X)`, additively.
* `Deformation.Examples.deformationLiftsEquivHom`: the bijection of
  [Stacks Project, Tag 0CK2] at a single deformation.
* `Deformation.Examples.deformationSelfMapsEquivDerivations`: the self-maps of the total space of
  a deformation over the base fixing the special fibre are the `k`-derivations of `𝒪_X`.
* `Deformation.Examples.fiberAutEquivSelfMapsOfBase`: the fibre automorphisms as self-maps, with
  the invertibility clause dropped, it being automatic.
* `Deformation.Examples.infinitesimalAutomorphismGroupMulEquivDerivations`: **`Inf(𝓓_X)` is the
  group of `k`-derivations of `𝒪_X`**, as an isomorphism of groups.

## Main results

* `Deformation.Examples.deformationLiftsEquivHom_add` and
  `Deformation.Examples.deformationSelfMapsEquivDerivations_symm_add`: addition of derivations is
  composition of self-maps.
* `Deformation.Examples.deformationSelfMapsEquivDerivations_comp`: the same read forwards, which
  is what the group isomorphism consumes.
* `Deformation.Examples.fiberAutEquivSelfMapsOfBase_mul`: the fibre-automorphism group law is
  composition of self-maps.

## The four terms

The `Inf(𝓓_X)` of the source is `Deformation.infinitesimalAutomorphismGroup` at the projection
of the deformation category of `X`. Here it is taken at an arbitrary point `xε` over an object of
`𝒞_Λ` with a dual-number coordinate; the canonical one, the trivial deformation over `k[ε]`, is
taken in `StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial`.

`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` is `AlgebraicGeometry.Scheme.naiveCotangentExt` at the structure
morphism of `X`, with `NL_{X/k}` the naive cotangent complex of [Stacks Project, Tag 0D0H], and
`Ω_{X/k}` is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` of that morphism — the
spelling the degree-zero identification of [Stacks Project, Tag 0D0J] lands in. The comparison
with the ringed-space sheaf of differentials, out of which the derivations of the fourth term are
maps, is `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`.

`Der_k(𝒪_X, 𝒪_X)` is `Deformation.Examples.schemeMorphismDerivations` at the identity of `X`.
That takes its coefficients in the pushforward of `𝒪_X` along the identity, which is `𝒪_X`: the
pushforward along an identity of ringed spaces is the identity functor, and the two sheaves of
modules are the same term, so the fourth term of the chain is the derivations of `𝒪_X` with
values in `𝒪_X`.

## Implementation notes

The chain is assembled from identifications that each leave the underlying morphism of schemes
alone, which is what lets the group law be checked once.
`Deformation.Examples.fiberAutEquivSelfMaps` sends an automorphism to its map on total spaces and
composes covariantly (`Deformation.Examples.fiberAutEquivSelfMaps_mul`); the invertibility clause
of its target is dropped because a self-map over the base fixing the special fibre is invertible
(`Deformation.Examples.isIso_of_fixes_specialMap_over_base`); and the bijection with the
derivations is `Stacks.Thickenings.derivationActionGlobalEquivOfBase`, whose value is the
modified lift, so the composition law is the one proved for that construction.

`𝒪_X` is written through `Deformation.Examples.structureSheafModules`, which ascribes
`SheafOfModules.unit` to `AlgebraicGeometry.Scheme.Modules`. The two are the same term, but
`AlgebraicGeometry.Scheme.Modules` is a `def` and instance search does not cross it, so without
the ascription the additive structure on the groups of homomorphisms is invisible.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H)
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- `𝒪_X` read as a sheaf of modules over itself, in the `AlgebraicGeometry.Scheme.Modules`
spelling. -/
abbrev structureSheafModules (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit (structureSheafRing Z.toRingedSpace)

/-- **The coefficients of `Der_k(𝒪_X, (𝟙_X)_*𝒪_X)` are the structure sheaf of `X`.** The
pushforward of 𝒪_X along the identity of `X` is 𝒪_X: pushforward along an identity of ringed
spaces is the identity functor, and the two sheaves of modules are the same term. So the fourth
term of the chain of [Stacks Project, Tag 0DY9] is the derivations of 𝒪_X with values in 𝒪_X. -/
theorem schemeMorphismPushforwardStructureSheaf_id (Z : Scheme.{u}) :
    schemeMorphismPushforwardStructureSheaf (𝟙 Z) = structureSheafModules Z :=
  rfl

section Hom

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- **The global homomorphisms `f^*Ω_{Y/k} ⟶ 𝒞_{X/X'}` are `Der_k(𝒪_Y, f_*N)`, additively**, for
any identification `ε` of the conormal sheaf with an `𝒪_X`-module `N`. This is
`Deformation.Examples.deformationHomSectionsTopDerivationsAddEquiv` read on the global
homomorphisms rather than on the sections of the sheaf of homomorphisms over the whole space, the
two being identified by `Deformation.Examples.deformationHomSectionsTopAddEquiv`. At `N = 𝒪_X`
the right-hand side is the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of
[Stacks Project, Tag 0E3V], which is the case the trivialisation of the conormal sheaf of a
first-order deformation supplies; a square-zero base of rank `n` gives the free `N` of rank `n`
instead. -/
def schemeMorphismLiftHomAddEquiv {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i]
    {N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ε : Stacks.Thickenings.immersionConormalSheaf i ≅ N) :
    (schemeMorphismPullbackCotangent f pY ⟶ Stacks.Thickenings.immersionConormalSheaf i)
      ≃+ Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
        ((RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom).obj N) :=
  (deformationHomSectionsTopAddEquiv f pY i).symm.trans
    (deformationHomSectionsTopDerivationsAddEquiv f pY i ε)

end Hom

section SelfMaps

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

attribute [local instance] residueSpecMap_isClosedImmersion
attribute [local instance] deformationSpecialMap_isClosedImmersion

/-- **The bijection of [Stacks Project, Tag 0CK2] at a single deformation.** The derivation data
`a^*Ω_{X/k} ⟶ 𝒞_{X/P.scheme}` are the self-maps of the total space of `P` over its base
restricting to the identity of `X`, by `θ ↦ θ ⬝ 𝟙`.

This is `Stacks.Thickenings.derivationActionGlobalEquivOfBase` at `Y' = X' = P.scheme`,
`j = i = P.specialMap`, `a = 𝟙_X` and `a' = 𝟙_{P.scheme}`. Its cartesian square is
`Deformation.Examples.SchemeDeformationCategory.specialCartesian` and its square-zero hypothesis
comes from the dual-number coordinate on the base. -/
def deformationLiftsEquivHom (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) :
    (Stacks.Smooth.pullbackCotangentSheaf X.hom (𝟙 X.left) ⟶
        Stacks.Thickenings.conormalModules P.specialMap) ≃
      { b' : P.scheme ⟶ P.scheme //
        b' ≫ P.toBase = P.toBase ∧ P.specialMap ≫ b' = 𝟙 X.left ≫ P.specialMap } :=
  Stacks.Thickenings.derivationActionGlobalEquivOfBase
    (i := P.specialMap) (j := P.specialMap) (k := residueSpecMap P.base)
    (h := X.hom) (h' := P.toBase) (g' := P.toBase)
    (a := 𝟙 X.left) (a' := 𝟙 P.scheme)
    (ker_sq_eq_bot_of_isPullback P.toBase P.specialCartesian
      (maximalIdeal_sq_eq_bot_of_dualNumberEquiv coordinate))
    P.specialCartesian
    (by rw [Category.id_comp]; exact P.specialCartesian.w)
    (by simp) (Category.id_comp _)

/-- **Addition of derivation data is composition of the self-maps they produce.** -/
theorem deformationLiftsEquivHom_add (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k)
    (θ η : Stacks.Smooth.pullbackCotangentSheaf X.hom (𝟙 X.left) ⟶
      Stacks.Thickenings.conormalModules P.specialMap) :
    (deformationLiftsEquivHom P coordinate (θ + η)).1
      = (deformationLiftsEquivHom P coordinate θ).1
          ≫ (deformationLiftsEquivHom P coordinate η).1 :=
  Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp _ _ _ _ _ θ η

/-- **The self-maps of the total space of a deformation over the base fixing the special fibre
are the `k`-derivations of `𝒪_X`.** The conormal sheaf of the special-fibre immersion is the
structure sheaf of `X` by `Deformation.Examples.deformationConormalIsoUnit`, so the derivation
data of `Deformation.Examples.deformationLiftsEquivHom` are the derivations. -/
def deformationSelfMapsEquivDerivations (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) :
    { e : P.scheme ⟶ P.scheme //
        e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap }
      ≃ schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom :=
  (Equiv.subtypeEquivRight fun _ => and_congr Iff.rfl (by rw [Category.id_comp])).trans
    ((deformationLiftsEquivHom P coordinate).symm.trans
      (schemeMorphismLiftHomAddEquiv (Λ := Λ) (k := k) (𝟙 X.left) X.hom P.specialMap
        (deformationConormalIsoUnit P coordinate)).toEquiv)

/-- **Addition of derivations is composition of self-maps.** -/
theorem deformationSelfMapsEquivDerivations_symm_add
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k)
    (θ η : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom) :
    ((deformationSelfMapsEquivDerivations P coordinate).symm (θ + η)).1
      = ((deformationSelfMapsEquivDerivations P coordinate).symm θ).1
          ≫ ((deformationSelfMapsEquivDerivations P coordinate).symm η).1 := by
  change (deformationLiftsEquivHom P coordinate
      ((schemeMorphismLiftHomAddEquiv (Λ := Λ) (k := k) (𝟙 X.left) X.hom P.specialMap
        (deformationConormalIsoUnit P coordinate)).symm (θ + η))).1 = _
  rw [map_add]
  exact deformationLiftsEquivHom_add P coordinate _ _

/-- **The fibre automorphisms as self-maps, with the invertibility clause dropped.** A self-map
of the total space over the base fixing the special fibre is invertible, by
`Deformation.Examples.isIso_of_fixes_specialMap_over_base`. -/
def fiberAutEquivSelfMapsOfBase (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Aut (deformationFiberObj P) ≃
      { e : P.scheme ⟶ P.scheme //
        e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap } :=
  (fiberAutEquivSelfMaps P).trans (Equiv.subtypeEquivRight fun e =>
    ⟨fun h => ⟨h.1, h.2.1⟩,
      fun h => ⟨h.1, h.2, isIso_of_fixes_specialMap_over_base P e h.1 h.2⟩⟩)

/-- **The fibre-automorphism group law is composition of self-maps**, by
`Deformation.Examples.fiberAutEquivSelfMaps_mul`, the dropping of the invertibility clause not
touching the underlying morphism. -/
theorem fiberAutEquivSelfMapsOfBase_mul (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (a b : Aut (deformationFiberObj P)) :
    (fiberAutEquivSelfMapsOfBase P (a * b)).1
      = (fiberAutEquivSelfMapsOfBase P a).1 ≫ (fiberAutEquivSelfMapsOfBase P b).1 :=
  fiberAutEquivSelfMaps_mul P a b

/-- **Composition of self-maps is addition of derivations**, which is
`Deformation.Examples.deformationSelfMapsEquivDerivations_symm_add` read forwards. -/
theorem deformationSelfMapsEquivDerivations_comp
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k)
    (c c₁ c₂ : { e : P.scheme ⟶ P.scheme //
      e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap })
    (hc : c.1 = c₁.1 ≫ c₂.1) :
    deformationSelfMapsEquivDerivations P coordinate c
      = deformationSelfMapsEquivDerivations P coordinate c₁
          + deformationSelfMapsEquivDerivations P coordinate c₂ := by
  set E := deformationSelfMapsEquivDerivations P coordinate with hE
  have h : E.symm (E c₁ + E c₂) = c :=
    Subtype.ext (by
      rw [hE, deformationSelfMapsEquivDerivations_symm_add]
      rw [← hE, E.symm_apply_apply, E.symm_apply_apply, hc])
  rw [← h, E.apply_symm_apply]

/-- **`Inf(𝓓_X)` is the group of `k`-derivations of `𝒪_X`.** The infinitesimal automorphism
group of the deformation category of a scheme `X` over `k`, at a point over an object of `𝒞_Λ`
carrying a dual-number coordinate, is isomorphic as a *group* to the additive group
`Der_k(𝒪_X, 𝒪_X)`.

The isomorphism is the composite of three steps that each leave the underlying morphism of
schemes alone: `Inf(𝓓_X)` is the whole automorphism group of the point in its fibre
(`Deformation.Examples.infinitesimalAutomorphismGroupMulEquivFiberAut`), those automorphisms are
the self-maps of the total space over the base fixing the special fibre
(`Deformation.Examples.fiberAutEquivSelfMapsOfBase`), and those self-maps are the derivations
(`Deformation.Examples.deformationSelfMapsEquivDerivations`). Multiplicativity is
`Deformation.Examples.fiberAutEquivSelfMapsOfBase_mul` followed by
`Deformation.Examples.deformationSelfMapsEquivDerivations_comp`, whose content is the composition
law `Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal` for modified
self-maps of a first-order thickening. -/
@[sga "1 III 6.1" "special case",
  sga "3 III 0.7" "(b), special case",
  sga "3 VIIA 1.5" "special case",
  sga "3 VIIA 2.5" "bijectivity of β"]
def infinitesimalAutomorphismGroupMulEquivDerivations
    (hp : IsPredeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (coordinate : xε.1.base ≃ₐ[Λ] DualNumber k)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi
      ≃* Multiplicative (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom) where
  toEquiv := ((infinitesimalAutomorphismGroupMulEquivFiberAut hp g e hpair i hi).toEquiv.trans
      (fiberAutEquivSelfMapsOfBase xε.1)).trans
    ((deformationSelfMapsEquivDerivations xε.1 coordinate).trans Multiplicative.ofAdd)
  map_mul' a b := by
    refine Eq.trans ?_ (ofAdd_add _ _)
    refine congrArg Multiplicative.ofAdd ?_
    change deformationSelfMapsEquivDerivations xε.1 coordinate
        (fiberAutEquivSelfMapsOfBase xε.1
          (infinitesimalAutomorphismGroupMulEquivFiberAut hp g e hpair i hi (a * b))) = _
    rw [map_mul]
    exact deformationSelfMapsEquivDerivations_comp xε.1 coordinate _ _ _
      (fiberAutEquivSelfMapsOfBase_mul xε.1 _ _)

end SelfMaps

end Deformation.Examples

end
