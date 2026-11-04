module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleNaturalIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf

/-!
# The pullback sections of `Ω_{X/Y}` on an étale scheme over `X`

Let `f : X ⟶ Y` be a morphism of schemes.  Two presheaves of abelian groups on the category of
schemes over `X` carry the relative differentials of `f`:

* the pullback-sections presheaf of Stacks 03DS of the module `Ω_{X/Y}`, whose value at
  `h : T ⟶ X` is `Γ(T, h⁺Ω_{X/Y})` and whose restriction maps are
  `AlgebraicGeometry.pullbackSectionsMap`; and
* the presheaf of relative differentials of Stacks 08RM read over `Y`, whose value at `h` is
  `Γ(T, Ω_{T/Y})` for the structure morphism `h ≫ f` and whose restriction maps are
  `AlgebraicGeometry.differentialSectionsMap`.

This module compares them.  The comparison at `h` is the canonical morphism
`h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of Stacks 01UV on global sections, it is natural in `T`, and by
Stacks 04BX it is an isomorphism as soon as `h` is étale.

## Main definitions

* `AlgebraicGeometry.differentialSectionsComparison` is the comparison
  `Γ(T, h⁺Ω_{X/Y}) ⟶ Γ(T, Ω_{T/Y})`, and
  `AlgebraicGeometry.differentialSectionsComparisonIso` is it as an isomorphism for `h` étale.
* `AlgebraicGeometry.etaleAssociatedDerivation` is `d_{T/Y}` read through that isomorphism, an
  additive map `Γ(T, 𝒪_T) →+ Γ(T, h⁺Ω_{X/Y})`.  These are the values of the derivation `d^a` of
  Stacks 04CS over the objects of the small étale site of `X`.

## Main results

* `AlgebraicGeometry.relativeDifferentialsMap_comp_pullbackComp`: the composition law of the
  canonical morphisms of Stacks 01UV along `T₀ ⟶ T₁ ⟶ X` over a fixed base, in naturality-square
  form.
* `AlgebraicGeometry.differentialSectionsComparison_naturality`: the comparison commutes with
  the restriction maps of the two presheaves, with
  `AlgebraicGeometry.differentialSectionsComparison_naturality'` the same square at an arbitrary
  spelling `j ≫ h₁ = h₀` of the composite structure morphism, which is the form a consumer
  indexing over the small étale site holds.
* `AlgebraicGeometry.isIso_differentialSectionsComparison`: for `h` étale the comparison is an
  isomorphism.  This is Stacks 04BX read on global sections.
* `AlgebraicGeometry.etaleAssociatedDerivation_mul` and
  `AlgebraicGeometry.etaleAssociatedDerivation_appTop_eq_zero`: the Leibniz rule for `d^a` over
  an étale scheme, and its vanishing on the global functions pulled back from `Y`.
* `AlgebraicGeometry.etaleAssociatedDerivation_naturality`: the values of `d^a` commute with
  restriction along a morphism of étale schemes over `X`.  This is what makes the family a
  morphism of presheaves on the small étale site.

## Implementation notes

Both restriction maps are instances of `Stacks.Sites.topUnitMap`, the map on global sections
attached to a morphism `j` of schemes and a comparison `j^*M ⟶ N`:
`Stacks.Sites.pullbackSectionsMap_eq_topUnitMap'` identifies the first and
`AlgebraicGeometry.differentialSectionsMap_eq_topUnitMap` the second.  Since `topUnitMap` turns
pre- and postcomposition on global sections into pre- and postcomposition of its comparison map
(`Stacks.Sites.comp_topUnitMap` and `Stacks.Sites.topUnitMap_comp`), naturality reduces to an
identity between morphisms of modules on the source, and that identity is exactly the
composition law `AlgebraicGeometry.relativeDifferentialsMap_comp_overBase` for the canonical
morphisms of Stacks 01UV.

The restriction map on the differentials side appears in the naturality statement as the
`Stacks.Sites.topUnitMap` it is equal to, rather than as
`AlgebraicGeometry.differentialSectionsMap` of an arrow of `CategoryTheory.Over Y`: writing that
arrow out as a `CategoryTheory.Over.homMk` exhausts the heartbeat budget while elaborating the
statement alone.  `AlgebraicGeometry.differentialSectionsMap_eq_topUnitMap` is what converts
between the two, and the consumer of this naturality square — the presheaf of sections of the
associated module — needs the `Stacks.Sites.topUnitMap` form in any case.

The source side keeps `AlgebraicGeometry.pullbackSectionsMap`, which is the restriction map of
`AlgebraicGeometry.quasiCoherentPresheafFunctor` on the nose and so is what that consumer holds.
Its arrow of `CategoryTheory.Over X` is a `CategoryTheory.Over.homMk` along a reflexivity proof,
and the `Scheme.Modules.pullbackCongr` it contributes is then the identity definitionally, which
is why the last step of the naturality proof closes by `exact` rather than by rewriting.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical morphism
  on relative differentials of a commutative square.
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the étale localization
  of relative differentials.
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM).
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Sites

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map of the presheaf of relative differentials of Stacks 08RM along a morphism of schemes
over the base is an instance of `Stacks.Sites.topUnitMap`: it is the canonical morphism of
Stacks 01UV, transposed and taken on global sections.

This is the counterpart for `AlgebraicGeometry.differentialSectionsMap` of
`Stacks.Sites.pullbackSectionsMap_eq_topUnitMap` for `AlgebraicGeometry.pullbackSectionsMap`. -/
theorem differentialSectionsMap_eq_topUnitMap {S : Scheme.{u}} {A Bb : Over S} (g : A ⟶ Bb)
    (h : g.left ≫ Bb.hom = A.hom ≫ 𝟙 S) :
    differentialSectionsMap g =
      topUnitMap g.left
        (Scheme.Hom.relativeDifferentialsMap g.left Bb.hom A.hom (𝟙 S) h) := by
  rw [topUnitMap, differentialSectionsMap, differentialsSectionMorphism]
  exact congrArg _ ((Scheme.Hom.relativeDifferentials A.hom).presheaf.map_id _)

/-- **The comparison of the pullback sections of `Ω_{X/Y}` with the relative differentials of the
source.**  For `h : T ⟶ X`, the canonical morphism `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of Stacks 01UV — for
the square with upper edge `h` and lower edge `𝟙 Y` — read on global sections. -/
noncomputable def differentialSectionsComparison {T : Scheme.{u}} (h : T ⟶ X) :
    Γ((Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials f), ⊤) ⟶
      Γ(Scheme.Hom.relativeDifferentials (h ≫ f), ⊤) :=
  (Scheme.Hom.relativeDifferentialsMap h f (h ≫ f) (𝟙 Y) (by simp)).app ⊤

/-- **The composition law of the canonical morphisms of Stacks 01UV along `T₀ ⟶ T₁ ⟶ X` over a
fixed base `Y`.**  Pulling back the comparison of `h₁ : T₁ ⟶ X` along `j : T₀ ⟶ T₁` and following
it by the comparison of `j` is the comparison of the composite `j ≫ h₁`, read through the
comparison of iterated pullback with pullback along the composite.

This is `AlgebraicGeometry.relativeDifferentialsMap_comp_overBase` with the arrows of
`CategoryTheory.Over Y` written out, and with the comparison of pullbacks moved to the other
side so that it reads as a naturality square. -/
theorem relativeDifferentialsMap_comp_pullbackComp {T₀ T₁ : Scheme.{u}} (j : T₀ ⟶ T₁)
    (h₁ : T₁ ⟶ X) :
    (Scheme.Modules.pullback j).map
          (Scheme.Hom.relativeDifferentialsMap h₁ f (h₁ ≫ f) (𝟙 Y) (by simp)) ≫
        Scheme.Hom.relativeDifferentialsMap j (h₁ ≫ f) ((j ≫ h₁) ≫ f) (𝟙 Y) (by simp) =
      (Scheme.Modules.pullbackComp j h₁).hom.app (Scheme.Hom.relativeDifferentials f) ≫
        Scheme.Hom.relativeDifferentialsMap (j ≫ h₁) f ((j ≫ h₁) ≫ f) (𝟙 Y) (by simp) := by
  have hcomp : (Scheme.Modules.pullbackComp j h₁).inv.app
          (Scheme.Hom.relativeDifferentials f) ≫
        (Scheme.Modules.pullback j).map
            (Scheme.Hom.relativeDifferentialsMap h₁ f (h₁ ≫ f) (𝟙 Y) (by simp)) ≫
          Scheme.Hom.relativeDifferentialsMap j (h₁ ≫ f) ((j ≫ h₁) ≫ f) (𝟙 Y) (by simp) =
      Scheme.Hom.relativeDifferentialsMap (j ≫ h₁) f ((j ≫ h₁) ≫ f) (𝟙 Y) (by simp) :=
    relativeDifferentialsMap_comp_overBase
      (X := (Over.mk ((j ≫ h₁) ≫ f) : Over Y)) (Y := (Over.mk (h₁ ≫ f) : Over Y))
      (Z := (Over.mk f : Over Y))
      (Over.homMk j (by simp) : (Over.mk ((j ≫ h₁) ≫ f) : Over Y) ⟶ Over.mk (h₁ ≫ f))
      (Over.homMk h₁ (by simp) : (Over.mk (h₁ ≫ f) : Over Y) ⟶ Over.mk f)
  rw [← hcomp]
  simp

/-- **The comparison of Stacks 01UV on global sections is natural in the scheme over `X`.**  The
square formed by the two comparisons and the restriction maps of the two presheaves — the
pullback-sections presheaf of Stacks 03DS of `Ω_{X/Y}` on `CategoryTheory.Over X`, and the
presheaf of relative differentials of Stacks 08RM on `CategoryTheory.Over Y` — commutes. -/
theorem differentialSectionsComparison_naturality {T₀ T₁ : Scheme.{u}} (j : T₀ ⟶ T₁)
    (h₁ : T₁ ⟶ X) :
    differentialSectionsComparison f h₁ ≫
        topUnitMap j
          (Scheme.Hom.relativeDifferentialsMap j (h₁ ≫ f) ((j ≫ h₁) ≫ f) (𝟙 Y) (by simp)) =
      pullbackSectionsMap (Scheme.Hom.relativeDifferentials f)
          (Over.homMk j rfl : (Over.mk (j ≫ h₁) : Over X) ⟶ Over.mk h₁) ≫
        differentialSectionsComparison f (j ≫ h₁) := by
  rw [differentialSectionsComparison, pullbackSectionsMap_eq_topUnitMap',
    differentialSectionsComparison, comp_topUnitMap, topUnitMap_comp]
  refine congrArg (topUnitMap j) ?_
  -- The comparison of pullbacks that `pullbackSectionsMap` carries is
  -- `(pullbackComp j h₁).hom` followed by a `pullbackCongr` along a reflexivity proof, and the
  -- latter is the identity definitionally, so this is the composition law of Stacks 01UV.
  exact relativeDifferentialsMap_comp_pullbackComp f j h₁

/-- **The naturality square at an arbitrary spelling of the composite structure morphism.**  A
consumer indexing over the small étale site of `X` holds a morphism `j : T₀ ⟶ T₁` together with
an equation `j ≫ h₁ = h₀`, not the composite `j ≫ h₁` itself; this is
`AlgebraicGeometry.differentialSectionsComparison_naturality` transported along that equation,
in the same way that `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_etale_eq`
restates Stacks 04BX at an arbitrary spelling. -/
theorem differentialSectionsComparison_naturality' {T₀ T₁ : Scheme.{u}} (j : T₀ ⟶ T₁)
    (h₁ : T₁ ⟶ X) (h₀ : T₀ ⟶ X) (hj : j ≫ h₁ = h₀) :
    differentialSectionsComparison f h₁ ≫
        topUnitMap j
          (Scheme.Hom.relativeDifferentialsMap j (h₁ ≫ f) (h₀ ≫ f) (𝟙 Y)
            (by rw [Category.comp_id, ← hj, Category.assoc])) =
      pullbackSectionsMap (Scheme.Hom.relativeDifferentials f)
          (Over.homMk j hj : (Over.mk h₀ : Over X) ⟶ Over.mk h₁) ≫
        differentialSectionsComparison f h₀ := by
  subst hj
  exact differentialSectionsComparison_naturality f j h₁

/-- **Stacks 04BX on global sections.**  For an étale `h : T ⟶ X` the comparison of the pullback
sections of `Ω_{X/Y}` with the global relative differentials of `T` over `Y` is an isomorphism,
because the canonical morphism `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` it is the sections of already is. -/
instance isIso_differentialSectionsComparison {T : Scheme.{u}} (h : T ⟶ X) [Etale h] :
    IsIso (differentialSectionsComparison f h) := by
  have : IsIso (Scheme.Hom.relativeDifferentialsMap h f (h ≫ f) (𝟙 Y)
      (show h ≫ f = (h ≫ f) ≫ 𝟙 Y from by simp)) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_etale_eq h f (h ≫ f) rfl
  exact inferInstanceAs (IsIso (Scheme.Modules.Hom.app
    (Scheme.Hom.relativeDifferentialsMap h f (h ≫ f) (𝟙 Y) (by simp)) ⊤))

/-- **The comparison of Stacks 04BX on global sections, as an isomorphism**
`Γ(T, h⁺Ω_{X/Y}) ≅ Γ(T, Ω_{T/Y})` for an étale `h : T ⟶ X`.

It is taken as the global sections of the module isomorphism
`AlgebraicGeometry.Scheme.Hom.etaleRelativeDifferentialsIso` rather than as
`CategoryTheory.asIso` of the comparison, so that *both* of its directions are the sections of
a morphism of `𝒪_T`-modules and are therefore `Γ(T, 𝒪_T)`-linear.  Linearity of the inverse is
what carries the Leibniz rule across the comparison. -/
noncomputable def differentialSectionsComparisonIso {T : Scheme.{u}} (h : T ⟶ X) [Etale h] :
    Γ((Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials f), ⊤) ≅
      Γ(Scheme.Hom.relativeDifferentials (h ≫ f), ⊤) :=
  sectionsTopIso (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl)

/-- The forward map of `AlgebraicGeometry.differentialSectionsComparisonIso` is the comparison
map `AlgebraicGeometry.differentialSectionsComparison`. -/
@[simp]
theorem differentialSectionsComparisonIso_hom {T : Scheme.{u}} (h : T ⟶ X) [Etale h] :
    (differentialSectionsComparisonIso f h).hom = differentialSectionsComparison f h :=
  rfl

/-! ### The universal derivation of `Ω_{X/Y}` read on an étale scheme over `X` -/

/-- **The value of the derivation `d^a` of Stacks 04CS over an étale `h : T ⟶ X`.**  The
universal `Y`-derivation `d_{T/Y}` of the global functions of `T`, read through the
isomorphism `Γ(T, Ω_{T/Y}) ≅ Γ(T, h⁺Ω_{X/Y})` of Stacks 04BX.

Over the objects of the small étale site of `X` these are the values of the `Y_étale`-derivation
`d^a : 𝒪_{X_étale} ⟶ (Ω_{X/Y})^a` whose existence is the first half of the proof of
Stacks 04CS. -/
noncomputable def etaleAssociatedDerivation {T : Scheme.{u}} (h : T ⟶ X) [Etale h] :
    Γ(T, (⊤ : T.Opens)) →+
      ToType Γ((Scheme.Modules.pullback h).obj (Scheme.Hom.relativeDifferentials f), ⊤) :=
  (Scheme.Modules.Hom.app
      (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl).inv ⊤).hom.comp
    (Scheme.Hom.universalRelativeDerivation (h ≫ f)).d

/-- `AlgebraicGeometry.etaleAssociatedDerivation` is the universal derivation `d_{T/Y}` followed
by the inverse of the comparison of Stacks 04BX. -/
theorem etaleAssociatedDerivation_apply {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (a : Γ(T, (⊤ : T.Opens))) :
    etaleAssociatedDerivation f h a =
      Scheme.Modules.Hom.app
          (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl).inv ⊤
        ((Scheme.Hom.universalRelativeDerivation (h ≫ f)).d a) :=
  rfl

/-- `d^a` vanishes on a function whose universal `Y`-derivation vanishes. -/
private theorem etaleAssociatedDerivation_eq_zero_of_d_eq_zero {T : Scheme.{u}} (h : T ⟶ X)
    [Etale h] {a : Γ(T, (⊤ : T.Opens))}
    (ha : (Scheme.Hom.universalRelativeDerivation (h ≫ f)).d a = 0) :
    etaleAssociatedDerivation f h a = 0 :=
  Eq.trans (congrArg
    (Scheme.Modules.Hom.app
      (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl).inv (⊤ : T.Opens)) ha)
    (map_zero _)

/-- **The Leibniz rule for `d^a` over an étale scheme.**  It is the Leibniz rule for the
universal `Y`-derivation of `T`, carried across the comparison of Stacks 04BX by the
`Γ(T, 𝒪_T)`-linearity of its inverse. -/
theorem etaleAssociatedDerivation_mul {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (a b : Γ(T, (⊤ : T.Opens))) :
    etaleAssociatedDerivation f h (a * b) =
      a • etaleAssociatedDerivation f h b + b • etaleAssociatedDerivation f h a := by
  refine Eq.trans (congrArg
    (Scheme.Modules.Hom.app
      (Scheme.Hom.etaleRelativeDifferentialsIso h f (h ≫ f) rfl).inv (⊤ : T.Opens))
    ((Scheme.Hom.universalRelativeDerivation (h ≫ f)).d_mul a b)) ?_
  refine Eq.trans (map_add _ _ _) ?_
  exact congrArg₂ (· + ·)
    (Scheme.Modules.Hom.app_smul _ a _) (Scheme.Modules.Hom.app_smul _ b _)

/-- **`d^a` annihilates the global functions pulled back from `Y`.**  Over an étale `h : T ⟶ X`
this is the corresponding property of the universal `Y`-derivation of `T`, which holds because
that derivation is taken relative to `(h ≫ f)⁻¹𝒪_Y`. -/
theorem etaleAssociatedDerivation_appTop_eq_zero {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (b : Γ(Y, (⊤ : Y.Opens))) :
    etaleAssociatedDerivation f h ((h ≫ f).appTop.hom b) = 0 :=
  etaleAssociatedDerivation_eq_zero_of_d_eq_zero f h
    (SheafOfModules.d_comorphism_eq_zero (h ≫ f)
      (Scheme.Hom.universalRelativeDerivation (h ≫ f)) ⊤ b)

/-- The comparison of Stacks 04BX recovers the universal derivation `d_{T/Y}` from the value of
`d^a`, since the two differ by the inverse of that comparison. -/
@[simp]
theorem differentialSectionsComparison_etaleAssociatedDerivation {T : Scheme.{u}} (h : T ⟶ X)
    [Etale h] (a : Γ(T, (⊤ : T.Opens))) :
    differentialSectionsComparison f h (etaleAssociatedDerivation f h a) =
      (Scheme.Hom.universalRelativeDerivation (h ≫ f)).d a :=
  (differentialSectionsComparisonIso f h).inv_hom_id_apply
    ((Scheme.Hom.universalRelativeDerivation (h ≫ f)).d a)

/-- **`d^a` annihilates the constants.**  The universal derivation does, and `d^a` is the
universal derivation followed by an additive map. -/
theorem etaleAssociatedDerivation_one {T : Scheme.{u}} (h : T ⟶ X) [Etale h] :
    etaleAssociatedDerivation f h 1 = 0 :=
  etaleAssociatedDerivation_eq_zero_of_d_eq_zero f h
    ((Scheme.Hom.universalRelativeDerivation (h ≫ f)).d_one _)

/-- **`d^a` annihilates the functions pulled back from an open of `Y`.**  If `h ≫ f` maps `T`
into the open `W` of `Y`, then `d^a` over `T` annihilates the image of `Γ(Y, W)` under the
comorphism of `h ≫ f`.  This is the vanishing of the universal `Y`-derivation of `T` on those
sections, which holds because that derivation is taken relative to `(h ≫ f)⁻¹𝒪_Y`.

`AlgebraicGeometry.etaleAssociatedDerivation_appTop_eq_zero` is the case `W = ⊤`. -/
theorem etaleAssociatedDerivation_appLE_eq_zero {T : Scheme.{u}} (h : T ⟶ X) [Etale h]
    (W : Y.Opens) (e : (⊤ : T.Opens) ≤ (h ≫ f) ⁻¹ᵁ W) (b : Γ(Y, W)) :
    etaleAssociatedDerivation f h (((h ≫ f).appLE W ⊤ e).hom b) = 0 := by
  refine etaleAssociatedDerivation_eq_zero_of_d_eq_zero f h ?_
  refine Eq.trans ((Scheme.Hom.universalRelativeDerivation (h ≫ f)).d_map
    (homOfLE e).op (((h ≫ f).app W).hom b)) ?_
  refine Eq.trans (congrArg _ (SheafOfModules.d_comorphism_eq_zero (h ≫ f)
    (Scheme.Hom.universalRelativeDerivation (h ≫ f)) W b)) (map_zero _)

/-- **The values of `d^a` are compatible with restriction along a morphism of étale schemes over
`X`.**  For `j : T₀ ⟶ T₁` with `j ≫ h₁ = h₀`, applying `d^a` over `T₁` and restricting to `T₀`
agrees with restricting the function and applying `d^a` over `T₀`.

This is the naturality that makes the family `AlgebraicGeometry.etaleAssociatedDerivation` a
morphism of presheaves on the small étale site of `X`.  The two ingredients are the naturality
of the comparison of Stacks 04BX and the characterizing property of the canonical morphism of
Stacks 01UV, which says that the canonical morphism carries `d_{T₁/Y} x` to `d_{T₀/Y}` of the
restriction of `x`. -/
theorem etaleAssociatedDerivation_naturality {T₀ T₁ : Scheme.{u}} (j : T₀ ⟶ T₁)
    (h₁ : T₁ ⟶ X) (h₀ : T₀ ⟶ X) (hj : j ≫ h₁ = h₀) [Etale h₁] [Etale h₀]
    (x : Γ(T₁, (⊤ : T₁.Opens))) :
    etaleAssociatedDerivation f h₀ (j.appTop.hom x) =
      pullbackSectionsMap (Scheme.Hom.relativeDifferentials f)
          (Over.homMk j hj : (Over.mk h₀ : Over X) ⟶ Over.mk h₁)
        (etaleAssociatedDerivation f h₁ x) := by
  have hcomm : j ≫ (h₁ ≫ f) = (h₀ ≫ f) ≫ 𝟙 Y := by
    rw [← hj]
    simp
  have hd : topUnitMap j
      (Scheme.Hom.relativeDifferentialsMap j (h₁ ≫ f) (h₀ ≫ f) (𝟙 Y) hcomm)
        ((Scheme.Hom.universalRelativeDerivation (h₁ ≫ f)).d x) =
      (Scheme.Hom.universalRelativeDerivation (h₀ ≫ f)).d (j.appTop.hom x) :=
    (Scheme.Hom.isRelativeDifferentialsMap_iff_eq j (h₁ ≫ f) (h₀ ≫ f) (𝟙 Y) hcomm _).mpr rfl ⊤ x
  have hnat := congrArg (fun m => m (etaleAssociatedDerivation f h₁ x))
    (differentialSectionsComparison_naturality' f j h₁ h₀ hj)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    differentialSectionsComparison_etaleAssociatedDerivation, hd] at hnat
  rw [etaleAssociatedDerivation_apply, hnat]
  exact (differentialSectionsComparisonIso f h₀).hom_inv_id_apply _

end AlgebraicGeometry

end
