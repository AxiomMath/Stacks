module

public import StacksFrontier.Algebra.Homology.ShortComplex.ShortExactMkOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ConormalShortExact

/-!
# The conormal sequence of a composition as the inverse image of a sequence of ideal sheaves

Let `W ⊆ X₀`, `Z ⊆ X₁` and `Y ⊆ X₂` be closed subspaces of algebraic spaces over a scheme `S`,
and let two commutative squares carry `W` into `Z` along `g₀ : X₀ ⟶ X₁` and `Z` into `Y` along
`g₁ : X₁ ⟶ X₂`.  The two maps of conormal modules of Stacks 04CP form a sequence

```
  f₀^*f₁^*𝒞_{Y/X₂} ⟶ f₀^*𝒞_{Z/X₁} ⟶ 𝒞_{W/X₀}
```

whose first arrow is the inverse image along `f₀ : W ⟶ Z` of the conormal map of the lower
square.  Each conormal map is a comparison of inverse images followed by the inverse image along
the inclusion `ι : W ⟶ X₀` of a map of defining ideal sheaves.  The comparison isomorphisms are
natural, so the whole sequence is isomorphic to the inverse image along `ι` of the sequence

```
  g₀^*g₁^*𝓘_Y ⟶ g₀^*𝓘_Z ⟶ 𝓘_W
```

of `𝒪_{X₀}`-modules, whose arrows are the inverse image along `g₀` of the map of defining ideal
sheaves of the lower square and the map of defining ideal sheaves of the upper square.  The two
sequences are therefore short exact together.

The conormal sequence `i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of Stacks 06BD, read on the copy of `Z`
inside the fibre product `Y ×_{Y'} Z'` as in
`AlgebraicGeometry.Space.universalThickeningCompConormalLeftMap` and
`AlgebraicGeometry.Space.universalThickeningCompConormalRightMap`, has this shape, with
`X₀ = Y ×_{Y'} Z'`, `X₁ = Z'` and `X₂ = Y'`.  So it is presented as the inverse image of a
sequence of modules on `Y ×_{Y'} Z'` built from maps of defining ideal sheaves alone.  No
identification of conormal modules is involved, only the naturality of the comparisons of
inverse images.

## Main results

* `AlgebraicGeometry.Space.map_conormalMap_comp_conormalPullbackComparison`: the first arrow,
  followed by the comparison at the middle term, is the inverse image along `ι` of
  `g₀^*(g₁^*𝓘_Y ⟶ 𝓘_Z)`.
* `AlgebraicGeometry.Space.shortExact_conormalSequence_iff_idealForm`: the sequence of conormal
  modules is short exact exactly when the inverse image of the sequence of ideal sheaves is.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Congr

variable {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (Z' : ClosedSubspaces B S hS X'.1)

/-- The map of defining ideal sheaves of a commutative square depends on the morphism of the
smaller spaces only through the commutativity proof. -/
theorem idealSheafMap_congr_left (g : X ⟶ X')
    {f f' : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS)} (hf : f = f')
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X Z ≫ g = f' ≫ subspaceInclusion B S hS X' Z') :
    idealSheafMap B S hS Z Z' g f hsq = idealSheafMap B S hS Z Z' g f' hsq' := by
  subst hf
  rfl

/-- The map of defining ideal sheaves of a commutative square, transported along an equality of
the morphisms of ambient spaces. -/
theorem idealSheafMap_congr_right {g g' : X ⟶ X'} (hg : g = g')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X Z ≫ g' = f ≫ subspaceInclusion B S hS X' Z') :
    idealSheafMap B S hS Z Z' g f hsq =
      (eqToHom (congrArg (fun h : X ⟶ X' => modulePullback B S hS h) hg)).app _ ≫
        idealSheafMap B S hS Z Z' g' f hsq' := by
  subst hg
  exact (Category.id_comp _).symm

end Congr

section Comparison

variable {X X' Y Y' : AlgebraicSpaces B S hS} {g : X ⟶ Y} {g' : X' ⟶ Y'} {c : Y' ⟶ Y}
  {c' : X' ⟶ X} (h : g' ≫ c = c' ≫ g)

/-- **Naturality of the comparison of inverse images along a commutative square**, the
composite `c'^*g^* ≅ (c' ≫ g)^* = (g' ≫ c)^* ≅ g'^*c^*` of the comparisons of Stacks 03LU. -/
theorem modulePullbackComp_square_naturality {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : M ⟶ N) :
    (modulePullback B S hS c').map ((modulePullback B S hS g).map φ) ≫
        (modulePullbackCompIso B S hS c' g).hom.app N ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) h.symm)).app N ≫
            (modulePullbackCompIso B S hS g' c).inv.app N =
      (modulePullbackCompIso B S hS c' g).hom.app M ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) h.symm)).app M ≫
          (modulePullbackCompIso B S hS g' c).inv.app M ≫
            (modulePullback B S hS g').map ((modulePullback B S hS c).map φ) := by
  have h1 := (modulePullbackCompIso B S hS c' g).hom.naturality φ
  have h2 := (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) h.symm)).naturality φ
  have h3 := (modulePullbackCompIso B S hS g' c).inv.naturality φ
  simp only [Functor.comp_map] at h1 h3
  rw [reassoc_of% h1, reassoc_of% h2, h3]

/-- `AlgebraicGeometry.Space.modulePullbackComp_square_naturality`, with the comparison grouped as
a single morphism. -/
theorem modulePullbackComp_square_naturality' {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : M ⟶ N) :
    (modulePullback B S hS c').map ((modulePullback B S hS g).map φ) ≫
        ((modulePullbackCompIso B S hS c' g).hom.app N ≫
          (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) h.symm)).app N ≫
            (modulePullbackCompIso B S hS g' c).inv.app N) =
      ((modulePullbackCompIso B S hS c' g).hom.app M ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) h.symm)).app M ≫
          (modulePullbackCompIso B S hS g' c).inv.app M) ≫
            (modulePullback B S hS g').map ((modulePullback B S hS c).map φ) := by
  rw [modulePullbackComp_square_naturality B S hS h φ]
  simp only [Category.assoc]

end Comparison

section Squares

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS} (W : ClosedSubspaces B S hS X₀.1)
  (Z : ClosedSubspaces B S hS X₁.1) (Y : ClosedSubspaces B S hS X₂.1)
  (g₀ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₂)
  (f₀ : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₀ : subspaceInclusion B S hS X₀ W ≫ g₀ = f₀ ≫ subspaceInclusion B S hS X₁ Z)
  (sq₁ : subspaceInclusion B S hS X₁ Z ≫ g₁ = f₁ ≫ subspaceInclusion B S hS X₂ Y)

/-- **The first arrow of the conormal sequence of two stacked squares, read at the middle term
through the comparison of inverse images, is an inverse image of a map of ideal sheaves.**  The
inverse image along `f₀` of the conormal map of the lower square, followed by the comparison
`f₀^*𝒞_{Z/X₁} ≅ ι^*g₀^*𝓘_Z` of the upper square, is a comparison isomorphism followed by the
inverse image along `ι` of `g₀^*(g₁^*𝓘_Y ⟶ 𝓘_Z)`. -/
theorem map_conormalMap_comp_conormalPullbackComparison :
    (modulePullback B S hS f₀).map (conormalMap B S hS Z Y g₁ f₁ sq₁) ≫
        conormalPullbackComparison B S hS W Z g₀ f₀ sq₀ =
      ((modulePullback B S hS f₀).map (conormalPullbackComparison B S hS Z Y g₁ f₁ sq₁) ≫
          (conormalPullbackCompIso B S hS W Z g₀ f₀ sq₀).hom.app
            ((modulePullback B S hS g₁).obj (definingIdealSheaf B S hS X₂ Y).toSheafOfModules)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).map
          ((modulePullback B S hS g₀).map (idealSheafMap B S hS Z Y g₁ f₁ sq₁)) := by
  have hnat := (conormalPullbackCompIso B S hS W Z g₀ f₀ sq₀).hom.naturality
    (idealSheafMap B S hS Z Y g₁ f₁ sq₁)
  refine (congrArg (fun t => (modulePullback B S hS f₀).map t ≫
    conormalPullbackComparison B S hS W Z g₀ f₀ sq₀) (conormalMap_eq B S hS Z Y g₁ f₁ sq₁)).trans ?_
  refine (congrArg (· ≫ conormalPullbackComparison B S hS W Z g₀ f₀ sq₀)
    ((modulePullback B S hS f₀).map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg ((modulePullback B S hS f₀).map
    (conormalPullbackComparison B S hS Z Y g₁ f₁ sq₁) ≫ ·) hnat

/-- **The conormal sequence of two stacked squares is short exact exactly when the inverse image
along the inclusion of `W` of the sequence of ideal sheaves `g₀^*g₁^*𝓘_Y ⟶ g₀^*𝓘_Z ⟶ 𝓘_W` is.**
-/
theorem shortExact_conormalSequence_iff_idealForm :
    (∃ h : (modulePullback B S hS f₀).map (conormalMap B S hS Z Y g₁ f₁ sq₁) ≫
        conormalMap B S hS W Z g₀ f₀ sq₀ = 0, (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).map
          ((modulePullback B S hS g₀).map (idealSheafMap B S hS Z Y g₁ f₁ sq₁)) ≫
        (show (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).obj
              ((modulePullback B S hS g₀).obj
                (definingIdealSheaf B S hS X₁ Z).toSheafOfModules) ⟶
            conormalModule B S hS X₀ W from
          (modulePullback B S hS (subspaceInclusion B S hS X₀ W)).map
            (idealSheafMap B S hS W Z g₀ f₀ sq₀)) = 0, (ShortComplex.mk _ _ h).ShortExact :=
  by
  have : IsIso (conormalPullbackComparison B S hS Z Y g₁ f₁ sq₁) :=
    isIso_conormalPullbackComparison B S hS Z Y g₁ f₁ sq₁
  have : IsIso (conormalPullbackComparison B S hS W Z g₀ f₀ sq₀) :=
    isIso_conormalPullbackComparison B S hS W Z g₀ f₀ sq₀
  refine ShortComplex.exists_shortExact_mk_iff_of_isIso _ _ _ _
    ((modulePullback B S hS f₀).map (conormalPullbackComparison B S hS Z Y g₁ f₁ sq₁) ≫
      (conormalPullbackCompIso B S hS W Z g₀ f₀ sq₀).hom.app
        ((modulePullback B S hS g₁).obj (definingIdealSheaf B S hS X₂ Y).toSheafOfModules))
    (conormalPullbackComparison B S hS W Z g₀ f₀ sq₀) ?_ ?_
  · exact map_conormalMap_comp_conormalPullbackComparison B S hS W Z Y g₀ g₁ f₀ f₁ sq₀ sq₁
  · exact conormalMap_eq B S hS W Z g₀ f₀ sq₀

end Squares

section AbstractLocalization

variable {X₀ X₁ X₂ X₀' X₁' X₂' : AlgebraicSpaces B S hS} {W' : AlgebraicSpaces B S hS}
  {g₀ : X₀ ⟶ X₁} {g₁ : X₁ ⟶ X₂} {c₀ : X₀' ⟶ X₀} {c₁ : X₁' ⟶ X₁} {c₂ : X₂' ⟶ X₂}
  {g₀' : X₀' ⟶ X₁'} {g₁' : X₁' ⟶ X₂'} (hc₀ : g₀' ≫ c₁ = c₀ ≫ g₀) (hc₁ : g₁' ≫ c₂ = c₁ ≫ g₁)
  {IY : Modules.{u, u} B S hS X₂.1 X₂.2} {IZ : Modules.{u, u} B S hS X₁.1 X₁.2}
  {IW : Modules.{u, u} B S hS X₀.1 X₀.2} {IY' : Modules.{u, u} B S hS X₂'.1 X₂'.2}
  {IZ' : Modules.{u, u} B S hS X₁'.1 X₁'.2} {IW' : Modules.{u, u} B S hS X₀'.1 X₀'.2}
  (φ₁ : (modulePullback B S hS g₁).obj IY ⟶ IZ) (φ₀ : (modulePullback B S hS g₀).obj IZ ⟶ IW)
  (φ₁' : (modulePullback B S hS g₁').obj IY' ⟶ IZ')
  (φ₀' : (modulePullback B S hS g₀').obj IZ' ⟶ IW')
  (ψ₂ : (modulePullback B S hS c₂).obj IY ⟶ IY') (ψ₁ : (modulePullback B S hS c₁).obj IZ ⟶ IZ')
  (ψ₀ : (modulePullback B S hS c₀).obj IW ⟶ IW') [IsIso ψ₂] [IsIso ψ₁] [IsIso ψ₀]
  {ι : W' ⟶ X₀'} {W : AlgebraicSpaces B S hS} {ιW : W ⟶ X₀} {d : W' ⟶ W} (hd : ι ≫ c₀ = d ≫ ιW)

include hc₀ hc₁ hd in
/-- **A two-arrow sequence of modules localizes along a compatible family of identifications.**
Let `g₁^*I_Y ⟶ I_Z` and `g₀^*I_Z ⟶ I_W` be maps of modules over a pair of composable morphisms of
algebraic spaces, and `g₁'^*I_Y' ⟶ I_Z'`, `g₀'^*I_Z' ⟶ I_W'` the corresponding maps over a second
pair, related to the first by squares `g_i' ≫ c_{i+1} = c_i ≫ g_i` and identifications
`ψ : c^*I ≅ I'` compatible with the maps.  Then for a commutative square `ι ≫ c₀ = d ≫ ι_W`, the
inverse image along `d` of `ι_W^*(g₀^*g₁^*I_Y ⟶ g₀^*I_Z ⟶ I_W)` is short exact exactly when
`ι^*(g₀'^*g₁'^*I_Y' ⟶ g₀'^*I_Z' ⟶ I_W')` is. -/
theorem shortExact_pullback_iff_of_compatible
    (H₁ : (modulePullback B S hS c₁).map φ₁ ≫ ψ₁ =
      (modulePullbackCompIso B S hS c₁ g₁).hom.app IY ≫
        (eqToHom (congrArg (fun k : X₁' ⟶ X₂ => modulePullback B S hS k) hc₁.symm)).app IY ≫
        (modulePullbackCompIso B S hS g₁' c₂).inv.app IY ≫
        (modulePullback B S hS g₁').map ψ₂ ≫ φ₁')
    (H₀ : (modulePullback B S hS c₀).map φ₀ ≫ ψ₀ =
      (modulePullbackCompIso B S hS c₀ g₀).hom.app IZ ≫
        (eqToHom (congrArg (fun k : X₀' ⟶ X₁ => modulePullback B S hS k) hc₀.symm)).app IZ ≫
        (modulePullbackCompIso B S hS g₀' c₁).inv.app IZ ≫
        (modulePullback B S hS g₀').map ψ₁ ≫ φ₀') :
    (∃ h : (modulePullback B S hS d).map ((modulePullback B S hS ιW).map
          ((modulePullback B S hS g₀).map φ₁)) ≫
        (modulePullback B S hS d).map ((modulePullback B S hS ιW).map φ₀) = 0,
        (ShortComplex.mk _ _ h).ShortExact) ↔
      ∃ h : (modulePullback B S hS ι).map ((modulePullback B S hS g₀').map φ₁') ≫
          (modulePullback B S hS ι).map φ₀' = 0,
        (ShortComplex.mk _ _ h).ShortExact :=
  ShortComplex.exists_shortExact_mk_iff_of_localization φ₁ φ₀ φ₁' φ₀' ψ₂ ψ₁ ψ₀
    (fun M => (modulePullbackCompIso B S hS c₀ g₀).hom.app M ≫
      (eqToHom (congrArg (fun k : X₀' ⟶ X₁ => modulePullback B S hS k) hc₀.symm)).app M ≫
        (modulePullbackCompIso B S hS g₀' c₁).inv.app M)
    (fun M => inferInstance)
    (fun f => modulePullbackComp_square_naturality' B S hS hc₀ f)
    (fun M => (modulePullbackCompIso B S hS c₁ g₁).hom.app M ≫
      (eqToHom (congrArg (fun k : X₁' ⟶ X₂ => modulePullback B S hS k) hc₁.symm)).app M ≫
        (modulePullbackCompIso B S hS g₁' c₂).inv.app M)
    (fun M => inferInstance)
    (fun M => (modulePullbackCompIso B S hS d ιW).hom.app M ≫
      (eqToHom (congrArg (fun k : W' ⟶ X₀ => modulePullback B S hS k) hd.symm)).app M ≫
        (modulePullbackCompIso B S hS ι c₀).inv.app M)
    (fun M => inferInstance)
    (fun f => modulePullbackComp_square_naturality' B S hS hd f)
    (H₁.trans (by simp only [Category.assoc])) (H₀.trans (by simp only [Category.assoc]))

include hc₀ hc₁ hd in
/-- **The ideal form of a sequence of modules is short exact once its localization is**, along a
faithful exact inverse image `d^*`: the inverse image along `d` of the sequence is identified
with the localized one by `AlgebraicGeometry.Space.shortExact_pullback_iff_of_compatible`, and
`d^*` reflects short exactness. -/
theorem shortExact_of_shortExact_localization [(modulePullback B S hS d).Faithful]
    [PreservesFiniteLimits (modulePullback B S hS d)]
    [PreservesFiniteColimits (modulePullback B S hS d)]
    (H₁ : (modulePullback B S hS c₁).map φ₁ ≫ ψ₁ =
      (modulePullbackCompIso B S hS c₁ g₁).hom.app IY ≫
        (eqToHom (congrArg (fun k : X₁' ⟶ X₂ => modulePullback B S hS k) hc₁.symm)).app IY ≫
        (modulePullbackCompIso B S hS g₁' c₂).inv.app IY ≫
        (modulePullback B S hS g₁').map ψ₂ ≫ φ₁')
    (H₀ : (modulePullback B S hS c₀).map φ₀ ≫ ψ₀ =
      (modulePullbackCompIso B S hS c₀ g₀).hom.app IZ ≫
        (eqToHom (congrArg (fun k : X₀' ⟶ X₁ => modulePullback B S hS k) hc₀.symm)).app IZ ≫
        (modulePullbackCompIso B S hS g₀' c₁).inv.app IZ ≫
        (modulePullback B S hS g₀').map ψ₁ ≫ φ₀')
    (h : ∃ h : (modulePullback B S hS ι).map ((modulePullback B S hS g₀').map φ₁') ≫
          (modulePullback B S hS ι).map φ₀' = 0,
        (ShortComplex.mk _ _ h).ShortExact) :
    ∃ h : (modulePullback B S hS ιW).map ((modulePullback B S hS g₀).map φ₁) ≫
        (modulePullback B S hS ιW).map φ₀ = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have : (modulePullback B S hS d).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS d).isLeftAdjoint
  have : (modulePullback B S hS d).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact ShortComplex.exists_shortExact_mk_of_map (modulePullback B S hS d) _ _
    ((shortExact_pullback_iff_of_compatible B S hS hc₀ hc₁ φ₁ φ₀ φ₁' φ₀' ψ₂ ψ₁ ψ₀ hd H₁ H₀).mpr h)

end AbstractLocalization

section Localization

variable {X₀ X₁ X₂ X₀' X₁' X₂' : AlgebraicSpaces B S hS} (W : ClosedSubspaces B S hS X₀.1)
  (Z : ClosedSubspaces B S hS X₁.1) (Y : ClosedSubspaces B S hS X₂.1)
  (g₀ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₂)
  (f₀ : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (f₁ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
  (sq₀ : subspaceInclusion B S hS X₀ W ≫ g₀ = f₀ ≫ subspaceInclusion B S hS X₁ Z)
  (sq₁ : subspaceInclusion B S hS X₁ Z ≫ g₁ = f₁ ≫ subspaceInclusion B S hS X₂ Y)
  (c₀ : X₀' ⟶ X₀) (c₁ : X₁' ⟶ X₁) (c₂ : X₂' ⟶ X₂) (g₀' : X₀' ⟶ X₁') (g₁' : X₁' ⟶ X₂')
  (hc₀ : g₀' ≫ c₁ = c₀ ≫ g₀) (hc₁ : g₁' ≫ c₂ = c₁ ≫ g₁)
  (f₀' : (⟨(preimageSubspace B S hS c₀ W).1.toFunctor, (preimageSubspace B S hS c₀ W).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶
    (⟨(preimageSubspace B S hS c₁ Z).1.toFunctor, (preimageSubspace B S hS c₁ Z).2.1⟩ :
      AlgebraicSpaces B S hS))
  (f₁' : (⟨(preimageSubspace B S hS c₁ Z).1.toFunctor, (preimageSubspace B S hS c₁ Z).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶
    (⟨(preimageSubspace B S hS c₂ Y).1.toFunctor, (preimageSubspace B S hS c₂ Y).2.1⟩ :
      AlgebraicSpaces B S hS))
  (sq₀' : subspaceInclusion B S hS X₀' (preimageSubspace B S hS c₀ W) ≫ g₀' =
    f₀' ≫ subspaceInclusion B S hS X₁' (preimageSubspace B S hS c₁ Z))
  (sq₁' : subspaceInclusion B S hS X₁' (preimageSubspace B S hS c₁ Z) ≫ g₁' =
    f₁' ≫ subspaceInclusion B S hS X₂' (preimageSubspace B S hS c₂ Y))

include sq₁ hc₁ sq₁' in
/-- **The map of ideal sheaves of the lower square restricts along the localization.**  On `X₁'`,
the inverse image along `c₁` of `g₁^*𝓘_Y ⟶ 𝓘_Z` followed by the identification
`c₁^*𝓘_Z ≅ 𝓘_{c₁⁻¹Z}` is the comparison `c₁^*g₁^* ≅ g₁'^*c₂^*` followed by the identification
`c₂^*𝓘_Y ≅ 𝓘_{c₂⁻¹Y}` and the map of ideal sheaves of the localized square. -/
theorem map_idealSheafMap_comp_idealSheafMap_preimage :
    (modulePullback B S hS c₁).map (idealSheafMap B S hS Z Y g₁ f₁ sq₁) ≫
        idealSheafMap B S hS (preimageSubspace B S hS c₁ Z) Z c₁
          (preimageProjection B S hS c₁ Z) (conormalEtaleRestrictionSquare B S hS c₁ Z) =
      (modulePullbackCompIso B S hS c₁ g₁).hom.app
          (definingIdealSheaf B S hS X₂ Y).toSheafOfModules ≫
        (eqToHom (congrArg (fun k : X₁' ⟶ X₂ => modulePullback B S hS k) hc₁.symm)).app
          (definingIdealSheaf B S hS X₂ Y).toSheafOfModules ≫
        (modulePullbackCompIso B S hS g₁' c₂).inv.app
          (definingIdealSheaf B S hS X₂ Y).toSheafOfModules ≫
        (modulePullback B S hS g₁').map
          (idealSheafMap B S hS (preimageSubspace B S hS c₂ Y) Y c₂
            (preimageProjection B S hS c₂ Y) (conormalEtaleRestrictionSquare B S hS c₂ Y)) ≫
        idealSheafMap B S hS (preimageSubspace B S hS c₁ Z) (preimageSubspace B S hS c₂ Y)
          g₁' f₁' sq₁' := by
  have hf : preimageProjection B S hS c₁ Z ≫ f₁ = f₁' ≫ preimageProjection B S hS c₂ Y := by
    have hmono : Mono (subspaceInclusion B S hS X₂ Y) :=
      (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono Y.1.ι))
    rw [← cancel_mono (subspaceInclusion B S hS X₂ Y)]
    simp only [Category.assoc]
    rw [← sq₁, ← Category.assoc, ← conormalEtaleRestrictionSquare B S hS c₁ Z, Category.assoc,
      ← hc₁, ← Category.assoc, sq₁', Category.assoc, conormalEtaleRestrictionSquare B S hS c₂ Y]
  have e₁ : subspaceInclusion B S hS X₁' (preimageSubspace B S hS c₁ Z) ≫ c₁ ≫ g₁ =
      (preimageProjection B S hS c₁ Z ≫ f₁) ≫ subspaceInclusion B S hS X₂ Y := by
    rw [← Category.assoc, conormalEtaleRestrictionSquare B S hS c₁ Z, Category.assoc, sq₁,
      Category.assoc]
  have e₂ : subspaceInclusion B S hS X₁' (preimageSubspace B S hS c₁ Z) ≫ g₁' ≫ c₂ =
      (preimageProjection B S hS c₁ Z ≫ f₁) ≫ subspaceInclusion B S hS X₂ Y := by
    rw [hc₁, e₁]
  have e₃ : subspaceInclusion B S hS X₁' (preimageSubspace B S hS c₁ Z) ≫ g₁' ≫ c₂ =
      (f₁' ≫ preimageProjection B S hS c₂ Y) ≫ subspaceInclusion B S hS X₂ Y := by
    rw [← Category.assoc, sq₁', Category.assoc, conormalEtaleRestrictionSquare B S hS c₂ Y,
      Category.assoc]
  have hA := idealSheafMap_comp B S hS c₁ g₁ (preimageSubspace B S hS c₁ Z) Z Y
    (preimageProjection B S hS c₁ Z) f₁ (conormalEtaleRestrictionSquare B S hS c₁ Z) sq₁ e₁
  have hB := idealSheafMap_comp B S hS g₁' c₂ (preimageSubspace B S hS c₁ Z)
    (preimageSubspace B S hS c₂ Y) Y f₁' (preimageProjection B S hS c₂ Y) sq₁'
    (conormalEtaleRestrictionSquare B S hS c₂ Y) e₃
  have hC := idealSheafMap_congr_right B S hS (preimageSubspace B S hS c₁ Z) Y hc₁.symm
    (preimageProjection B S hS c₁ Z ≫ f₁) e₁ e₂
  have hD := idealSheafMap_congr_left B S hS (preimageSubspace B S hS c₁ Z) Y (g₁' ≫ c₂) hf
    e₂ e₃
  have h1 := (congrArg (fun t => (modulePullbackCompIso B S hS c₁ g₁).hom.app
      (definingIdealSheaf B S hS X₂ Y).toSheafOfModules ≫ t) hA).trans
    (Iso.hom_inv_id_app_assoc (modulePullbackCompIso B S hS c₁ g₁) _ _)
  refine h1.symm.trans ?_
  refine (congrArg (fun t => (modulePullbackCompIso B S hS c₁ g₁).hom.app
      (definingIdealSheaf B S hS X₂ Y).toSheafOfModules ≫ t) (hC.trans
        (congrArg (fun t => _ ≫ t) (hD.trans hB)))).trans ?_
  rfl


end Localization

end AlgebraicGeometry.Space

end
