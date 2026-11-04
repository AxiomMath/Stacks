module

public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricallyIrreducibleFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeGenericPoints
import StacksFrontier.AlgebraicGeometry.Properties.QuasiAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When the Stein factorization of a proper morphism over a normal base is trivial

Let `f : X ⟶ S` be a proper morphism from a reduced scheme to a normal integral scheme, let `ξ`
be the generic point of `S`, and assume that every generic point of an irreducible component of
`X` maps to `ξ` and that the generic fibre has no global functions beyond the residue field,
`H⁰(X_ξ, 𝒪) = κ(ξ)`.  Then the second factor `π : S' ⟶ S` of the Stein factorization
`X ⟶ S' ⟶ S` is an isomorphism, so that `f_*𝒪_X = 𝒪_S`.

The argument is the one of [Stacks, Tag 0AY8].  The intermediate scheme `S'` is reduced because
`X` is ([Stacks, Tag 0AXN]).  Its generic fibre over `ξ` is the relative spectrum of
`H⁰(X_ξ, 𝒪) = κ(ξ)`, by flat base change for the factorization along the flat morphism
`Spec κ(ξ) ⟶ S`, so `π` has exactly one point over `ξ`; since every generic point of `S'` lies
over `ξ` ([Stacks, Tag 0AXP] together with the hypothesis on the generic points of `X`), `S'` has
a single generic point and is therefore integral.  At that point `π` is an isomorphism on local
rings, so `π` is birational, and an integral birational morphism onto a normal integral scheme is
an isomorphism ([Stacks, Tag 0AB1]).

## Main results

* `Stacks.SteinFactorization.isIso_fromNormalization_of_isIso_appTop`: for a proper morphism to
  an affine base whose map on global sections is an isomorphism, the second factor of the Stein
  factorization is an isomorphism.
* `Stacks.SteinFactorization.isIso_fiberToSpecResidueField_fromNormalization_genericPoint`: the
  generic fibre of the second factor is the spectrum of the residue field at the generic point.
* `Stacks.SteinFactorization.isIso_fromNormalization_of_isNormal`: under the hypotheses of
  [Stacks, Tag 0AY8] the second factor of the Stein factorization is an isomorphism, that is,
  `S' = S`.
* `Stacks.SteinFactorization.isIso_c_of_isNormal`: the first conclusion of [Stacks, Tag 0AY8],
  that `f_*𝒪_X = 𝒪_S`.
* `Stacks.SteinFactorization.surjective_of_isNormal`: the nonemptiness half of the second
  conclusion of [Stacks, Tag 0AY8], that every fibre of `f` is nonempty.
* `Stacks.SteinFactorization`
  `.geometricallyConnected_fiberToSpecResidueField_genericPoint_of_isNormal`: the fibre over the
  generic point is geometrically connected.
* `Stacks.SteinFactorization.geometricallyConnected_of_isNormal`: **the second conclusion** of
  [Stacks, Tag 0AY8], that `f` has geometrically connected fibres.
* `Stacks.SteinFactorization.geometricallyConnected_of_isNormal_of_extendsOverNeighbourhood`: the
  same conclusion over the stronger hypothesis that *every* function on a fibre extends, not only
  the idempotents.

## Implementation notes

The equality `H⁰(X_ξ, 𝒪) = κ(ξ)` is expressed by invertibility of the canonical ring map
`κ(ξ) ⟶ Γ(X_ξ, 𝒪_{X_ξ})`, and `f_*𝒪_X = 𝒪_S` by invertibility of the canonical map of sheaves
`𝒪_S ⟶ f_*𝒪_X`, which is `AlgebraicGeometry.Scheme.Hom.c`.  Membership in `genericPoints X`
means being the generic point of an irreducible component of `X`.

The second conclusion is deduced as in the source from clause (1) of [Stacks, Tag 03H2],
transported along the isomorphism `π : S' ⟶ S`; that clause is
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`, which rests on
[Stacks, Tag 0G7X] (`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`). Since
Tag 0AY8 does not assume `S` Noetherian, this uses the general case of Tag 0G7X. Over `ξ` itself
no such input is needed: the local ring of `S` at `ξ` is a field and flat base change suffices.

## References

* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0AXN](https://stacks.math.columbia.edu/tag/0AXN)
* [Stacks Project, Tag 0AXP](https://stacks.math.columbia.edu/tag/0AXP)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SteinFactorization

open Stacks.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The scheme-theoretic fibre morphism is the second projection of the defining pullback
square. -/
private theorem fiberToSpecResidueField_eq_pullback_snd {A B : Scheme.{u}} (h : A ⟶ B) (b : B) :
    h.fiberToSpecResidueField b = pullback.snd h (B.fromSpecResidueField b) := rfl

/-- A morphism between affine schemes which is an isomorphism on global sections is an
isomorphism: as an arrow it is isomorphic to the spectrum of the map on global sections.  An alias
of `AlgebraicGeometry.isIso_of_isAffine_of_isIso_appTop`. -/
private alias isIso_of_isAffine_of_isIso_appTop :=
  AlgebraicGeometry.isIso_of_isAffine_of_isIso_appTop

/-- An isomorphism of schemes is an isomorphism on the structure sheaves. -/
private theorem isIso_c_of_isIso {A B : Scheme.{u}} (h : A ⟶ B) [IsIso h] : IsIso h.c :=
  PresheafedSpace.c_isIso_of_iso h.toPshHom

/-- The condition `h_*𝒪 = 𝒪` is stable under composition: the map of a composite is the
composite of one map with the pushforward of the other. -/
private theorem isIso_c_comp {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C)
    (hg : IsIso g.c) (hh : IsIso h.c) : IsIso (g ≫ h).c :=
  have := hg
  have := hh
  (asIso h.c ≪≫
    (TopCat.Presheaf.pushforward CommRingCat h.base).mapIso (asIso g.c)).isIso_hom

/-- The morphism `Spec κ(ξ) ⟶ S` from the generic point of an integral scheme is flat. -/
private theorem flat_fromSpecResidueField_genericPoint (S : Scheme.{u}) [IsIntegral S] :
    Flat (S.fromSpecResidueField (genericPoint S)) :=
  have : IsIso (S.residue (genericPoint S)) := AlgebraicGeometry.isIso_residue_genericPoint S
  flat_fromSpecResidueField_of_isIso_residue (genericPoint S)

/-- For a proper morphism `h : X ⟶ T` onto an affine scheme with `Γ(T, ⊤) ⟶ Γ(X, ⊤)` an
isomorphism, the second factor of the Stein factorization of `h` is an isomorphism: the relative
normalization of an affine scheme is affine, its global sections are those of `X` because `h` is
universally closed, and those are the global sections of `T` by hypothesis. -/
public theorem isIso_fromNormalization_of_isIso_appTop {T : Scheme.{u}} (h : X ⟶ T) [IsProper h]
    [IsAffine T] (hΓ : IsIso h.appTop) : IsIso h.fromNormalization := by
  have : IsIso h.toNormalization.appTop := by
    have h₀ := Scheme.Hom.isIso_toNormalization_app h (isAffineOpen_top T)
    change IsIso (h.toNormalization.app ⊤)
    rwa [Scheme.Hom.preimage_top] at h₀
  have : IsIso (h.fromNormalization.appTop ≫ h.toNormalization.appTop) := by
    rw [← Scheme.Hom.comp_appTop, Scheme.Hom.toNormalization_fromNormalization]
    exact hΓ
  have : IsIso h.fromNormalization.appTop :=
    IsIso.of_isIso_comp_right _ h.toNormalization.appTop
  exact isIso_of_isAffine_of_isIso_appTop h.fromNormalization inferInstance

/-- For a proper morphism `f : X ⟶ S` onto an integral scheme with `H⁰(X_ξ, 𝒪) = κ(ξ)` at the
generic point `ξ`, the fibre of the second factor `π : S' ⟶ S` of the Stein factorization over
`ξ` is `Spec κ(ξ)`.

The morphism `Spec κ(ξ) ⟶ S` is flat, because the local ring of `S` at `ξ` is already a field, so
forming the Stein factorization commutes with base change along it
(`Stacks.SteinFactorization.isIso_normalizationPullback`); the fibre of `π` over `ξ` is therefore
the intermediate scheme of the factorization of `X_ξ ⟶ Spec κ(ξ)`, which is
`Spec H⁰(X_ξ, 𝒪) = Spec κ(ξ)`. -/
public theorem isIso_fiberToSpecResidueField_fromNormalization_genericPoint (f : X ⟶ S)
    [IsProper f] [IsIntegral S]
    (hΓ : IsIso (f.fiberToSpecResidueField (genericPoint S)).appTop) :
    IsIso (f.fromNormalization.fiberToSpecResidueField (genericPoint S)) := by
  rw [fiberToSpecResidueField_eq_pullback_snd] at hΓ ⊢
  have := flat_fromSpecResidueField_genericPoint S
  have hbase :
      IsIso (pullback.snd f (S.fromSpecResidueField (genericPoint S))).fromNormalization :=
    isIso_fromNormalization_of_isIso_appTop _ hΓ
  have : IsIso (f.normalizationPullback (S.fromSpecResidueField (genericPoint S))) :=
    isIso_normalizationPullback f (S.fromSpecResidueField (genericPoint S))
  have : IsIso (f.normalizationPullback (S.fromSpecResidueField (genericPoint S)) ≫
      pullback.snd f.fromNormalization (S.fromSpecResidueField (genericPoint S))) := by
    rw [Scheme.Hom.normalizationPullback_snd]
    exact hbase
  exact IsIso.of_isIso_comp_left
    (f.normalizationPullback (S.fromSpecResidueField (genericPoint S))) _

/-- **The heart of [Stacks, Tag 0AY8].**  Let `f : X ⟶ S` be a proper morphism from a reduced
scheme onto a normal integral scheme with generic point `ξ`.  If every generic point of an
irreducible component of `X` maps to `ξ` and `H⁰(X_ξ, 𝒪) = κ(ξ)`, then the second factor
`π : S' ⟶ S` of the Stein factorization of `f` is an isomorphism.

The intermediate scheme `S'` is reduced, its generic points all lie over `ξ`, and it has a single
point over `ξ`; so `S'` is integral with the same generic point data as `S`, hence `π` is
birational, and an integral birational morphism onto a normal integral scheme is an
isomorphism. -/
public theorem isIso_fromNormalization_of_isNormal (f : X ⟶ S) [IsProper f] [IsIntegral S]
    [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso (f.fiberToSpecResidueField (genericPoint S)).appTop) :
    IsIso f.fromNormalization := by
  have hfib : IsIso (f.fromNormalization.fiberToSpecResidueField (genericPoint S)) :=
    isIso_fiberToSpecResidueField_fromNormalization_genericPoint f hΓ
  -- the fibre of `π` over `ξ` is a one-point scheme, since it is `Spec κ(ξ)`
  have : Subsingleton (f.fromNormalization.fiber (genericPoint S)) :=
    (Scheme.homeoOfIso
      (asIso (f.fromNormalization.fiberToSpecResidueField
        (genericPoint S)))).injective.subsingleton
  have hne : Nonempty f.normalization :=
    ⟨f.fromNormalization.fiberι (genericPoint S)
      ((asIso (f.fromNormalization.fiberToSpecResidueField (genericPoint S))).inv
        (IsLocalRing.closedPoint (S.residueField (genericPoint S))))⟩
  -- every generic point of `S'` lies over `ξ`
  have hmaps : ∀ z : f.normalization, z ∈ genericPoints f.normalization →
      f.fromNormalization z = genericPoint S := by
    intro z hz
    obtain ⟨y, T, hT, hyT, hy⟩ :=
      AlgebraicGeometry.exists_genericPoint_irreducibleComponent_mapping_to f
        (x := z) (Z := closure {z}) hz rfl
    have hyg : y ∈ genericPoints X := by
      change closure {y} ∈ irreducibleComponents X
      rw [hyT]
      exact hT
    rw [← hy, ← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact hgen y hyg
  -- hence the generic points of `S'` form a single point
  have hsubpre : (f.fromNormalization ⁻¹' {genericPoint S}).Subsingleton := by
    intro a ha b hb
    have h₀ := Subsingleton.elim
      ((f.fromNormalization.fiberHomeo (genericPoint S)).symm ⟨a, ha⟩)
      ((f.fromNormalization.fiberHomeo (genericPoint S)).symm ⟨b, hb⟩)
    have h₁ := congrArg (f.fromNormalization.fiberHomeo (genericPoint S)) h₀
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h₁
    exact congrArg Subtype.val h₁
  have hgpsub : (genericPoints f.normalization).Subsingleton :=
    hsubpre.anti fun z hz ↦ Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (hmaps z hz))
  obtain ⟨z₀, hz₀⟩ : (genericPoints f.normalization).Nonempty := by
    obtain ⟨w⟩ := hne
    exact ⟨_, (genericPoints.ofComponent (⟨irreducibleComponent w,
      irreducibleComponent_mem_irreducibleComponents w⟩ :
        irreducibleComponents f.normalization)).2⟩
  have hsingle : genericPoints f.normalization = {z₀} := hgpsub.eq_singleton_of_mem hz₀
  -- so `S'` is irreducible, and being reduced it is integral
  have : IrreducibleSpace f.normalization := by
    have hcl : closure ({z₀} : Set f.normalization) = Set.univ := by
      rw [← hsingle]
      exact genericPoints.closure
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  have : IsIntegral f.normalization :=
    isIntegral_of_irreducibleSpace_of_isReduced f.normalization
  have hz₀eq : z₀ = genericPoint f.normalization := by
    have hsingle' := hsingle
    rw [genericPoints_eq_singleton] at hsingle'
    exact (Set.singleton_eq_singleton_iff.mp hsingle').symm
  have hpt : f.fromNormalization z₀ = genericPoint S := hmaps z₀ hz₀
  -- `π` is an isomorphism on local rings at the generic point: both residue maps are
  -- isomorphisms, and so is the induced map of residue fields because the fibre is `Spec κ(ξ)`
  have hstalk₀ : IsIso (f.fromNormalization.stalkMap z₀) := by
    have : IsIso (f.fromNormalization.fiberToSpecResidueField (f.fromNormalization z₀)) := by
      rw [hpt]; exact hfib
    have : IsIso (f.fromNormalization.residueFieldMap z₀) :=
      AlgebraicGeometry.isIso_residueFieldMap_of_isIso_fiberToSpecResidueField
        f.fromNormalization z₀
    have : IsIso (S.residue (f.fromNormalization z₀)) := by
      rw [hpt]; exact AlgebraicGeometry.isIso_residue_genericPoint S
    have : IsIso (f.normalization.residue z₀) := by
      rw [hz₀eq]; exact AlgebraicGeometry.isIso_residue_genericPoint f.normalization
    have hnat : IsIso (S.residue (f.fromNormalization z₀) ≫
        f.fromNormalization.residueFieldMap z₀) := inferInstance
    rw [Scheme.residue_residueFieldMap] at hnat
    have := hnat
    exact IsIso.of_isIso_comp_right _ (f.normalization.residue z₀)
  have hstalk : ∀ z : f.normalization, z ∈ genericPoints f.normalization →
      IsIso (f.fromNormalization.stalkMap z) := by
    intro z hz
    rw [hsingle, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hstalk₀
  -- and it matches up the generic points
  have hbij : Set.BijOn f.fromNormalization (genericPoints f.normalization)
      (genericPoints S) := by
    have hb : Set.BijOn f.fromNormalization {z₀} (f.fromNormalization '' {z₀}) :=
      (Set.injOn_singleton _ _).bijOn_image
    rw [Set.image_singleton, hpt] at hb
    rw [hsingle, genericPoints_eq_singleton]
    exact hb
  exact AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal f.fromNormalization
    (AlgebraicGeometry.isBirational_of_bijOn_of_isIso_stalkMap _ hbij hstalk)

/-- Under the hypotheses of Tag 0AY8, with the hypothesis on the generic fibre phrased through
`Scheme.ΓSpecIso`, the second factor of the Stein factorization is an isomorphism. -/
private theorem isIso_fromNormalization_of_isNormal_of_isIso_inv_comp
    (f : X ⟶ S) [IsProper f] [IsIntegral S] [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop)) :
    IsIso f.fromNormalization :=
  isIso_fromNormalization_of_isNormal f hgen
    (IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv _)

/-- If the second factor of the Stein factorization is an isomorphism, then `f` is geometrically
connected as soon as its first factor is. -/
private theorem geometricallyConnected_of_isIso_fromNormalization (f : X ⟶ S) [IsProper f]
    [IsIso f.fromNormalization] (h : GeometricallyConnected f.toNormalization) :
    GeometricallyConnected f := by
  have : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h : GeometricallyConnected (f.toNormalization ≫ f.fromNormalization) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyConnected
      f.toNormalization f.fromNormalization).mpr h
  rwa [Scheme.Hom.toNormalization_fromNormalization] at h

/-- **Stacks Project, Tag 0AY8, first conclusion.**  Let `f : X ⟶ S` be a proper morphism from a
reduced scheme onto a normal integral scheme with generic point `ξ`.  If every generic point of
an irreducible component of `X` maps to `ξ` and `H⁰(X_ξ, 𝒪) = κ(ξ)`, then `f_*𝒪_X = 𝒪_S`.

The second factor of the Stein factorization is an isomorphism, and the first already satisfies
`f'_*𝒪_X = 𝒪_{S'}` by clause (3) of [Stacks, Tag 03H2]. -/
@[stacks 0AY8 "pushforward of the structure sheaf"]
public theorem isIso_c_of_isNormal (f : X ⟶ S) [IsProper f] [IsIntegral S]
    [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop)) :
    IsIso f.c := by
  have : IsIso f.fromNormalization :=
    isIso_fromNormalization_of_isNormal_of_isIso_inv_comp f hgen hΓ
  have h := isIso_c_comp f.toNormalization f.fromNormalization
    (isIso_c_toNormalization_of_isProper f) (isIso_c_of_isIso f.fromNormalization)
  rwa [Scheme.Hom.toNormalization_fromNormalization] at h

/-- **The nonemptiness half of the second conclusion of [Stacks, Tag 0AY8].**  Under the
hypotheses of Tag 0AY8 every fibre of `f` is nonempty, that is, `f` is surjective.

Once `f_*𝒪_X = 𝒪_S` is known this is immediate: over a point outside the image of the
universally closed `f` the sections of `𝒪_S` would have to vanish on a nonempty open. -/
public theorem surjective_of_isNormal (f : X ⟶ S) [IsProper f] [IsIntegral S]
    [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop)) :
    Surjective f :=
  AlgebraicGeometry.VectorBundleCodimensionOne.surjective_of_isIso_cMap f
    (isIso_c_of_isNormal f hgen hΓ)

/-- **The second conclusion of [Stacks, Tag 0AY8] at the generic point.**  Under the
hypotheses of Tag 0AY8 the fibre of `f` over the generic point `ξ` of `S` is geometrically
connected.

Once `f_*𝒪_X = 𝒪_S` is known, this is flat base change along the flat morphism
`Spec κ(ξ) ⟶ S` followed by [Stacks, Tag 0FD1]; no form of [Stacks, Tag 0G7X] is needed. -/
public theorem geometricallyConnected_fiberToSpecResidueField_genericPoint_of_isNormal
    (f : X ⟶ S) [IsProper f] [IsIntegral S] [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop)) :
    GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S)) := by
  have := flat_fromSpecResidueField_genericPoint S
  exact geometricallyConnected_fiberToSpecResidueField_of_flat f (genericPoint S)
    (isIso_c_of_isNormal f hgen hΓ)

/-- **Stacks Project, Tag 0AY8, second conclusion, reduced to [Stacks, Tag 0G7X].**  Under the
hypotheses of Tag 0AY8, `f` has geometrically connected fibres provided that every function on
every fibre of the first factor of the Stein factorization extends over a neighbourhood of its
base point.

The second factor of the Stein factorization is an isomorphism, so the fibres of `f` are those of
the first factor, whose geometric connectedness is clause (1) of [Stacks, Tag 03H2]; here that
clause is deduced from the extension hypothesis `he`. -/
public theorem geometricallyConnected_of_isNormal_of_extendsOverNeighbourhood
    (f : X ⟶ S) [IsProper f] [IsIntegral S] [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop))
    (he : ∀ (s : f.normalization) (e : Γ(f.toNormalization.fiber s, ⊤)),
      Fibres.ExtendsOverNeighbourhood f.toNormalization s e) :
    GeometricallyConnected f := by
  have : IsIso f.fromNormalization :=
    isIso_fromNormalization_of_isNormal_of_isIso_inv_comp f hgen hΓ
  exact geometricallyConnected_of_isIso_fromNormalization f
    (geometricallyConnected_toNormalization_of_extendsOverNeighbourhood f he)

/-- **Stacks Project, Tag 0AY8, the second conclusion.**  Under the hypotheses of Tag 0AY8 — `f`
proper, `S` integral and normal, `X` reduced, every generic point of `X` over the generic point
`ξ` of `S`, and `H⁰(X_ξ, 𝒪) = κ(ξ)` — the morphism `f` has geometrically connected fibres.

The proof follows the source: the second factor `π : S' ⟶ S` of the Stein factorization is an
isomorphism
(`Stacks.SteinFactorization.isIso_fromNormalization_of_isNormal`), so the fibres of `f` are those
of the first factor, and their geometric connectedness is clause (1) of [Stacks, Tag 03H2],
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`.

The first conclusion, `f_*𝒪_X = 𝒪_S`, is `Stacks.SteinFactorization.isIso_c_of_isNormal`. -/
@[stacks 0AY8 "the second conclusion, that f has geometrically connected fibres.  The first \
  conclusion, f_*𝒪_X = 𝒪_S, is isIso_c_of_isNormal", ega "III 4.3.8" "special case"]
public theorem geometricallyConnected_of_isNormal
    (f : X ⟶ S) [IsProper f] [IsIntegral S] [AlgebraicGeometry.IsNormal S] [IsReduced X]
    (hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : IsIso ((Scheme.ΓSpecIso (S.residueField (genericPoint S))).inv ≫
      (f.fiberToSpecResidueField (genericPoint S)).appTop)) :
    GeometricallyConnected f := by
  have : IsIso f.fromNormalization :=
    isIso_fromNormalization_of_isNormal_of_isIso_inv_comp f hgen hΓ
  have := isProper_toNormalization f
  exact geometricallyConnected_of_isIso_fromNormalization f
    (geometricallyConnected_toNormalization_of_isProper f)

end Stacks.SteinFactorization
