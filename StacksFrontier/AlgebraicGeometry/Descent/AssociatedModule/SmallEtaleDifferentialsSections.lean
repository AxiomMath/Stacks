module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DifferentialSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleDescentDatum

/-!
# Global sections of relative differentials along an étale morphism

Let `f : X ⟶ Y` be a morphism of schemes and let `t : T ⟶ X` be étale.  The canonical map
`t^*Ω_{X/Y} ⟶ Ω_{T/Y}` of Stacks 01UV is an isomorphism (Stacks 04BX), so on global sections it
identifies the value at `T` of the pullback-sections presheaf of `Ω_{X/Y}` — the presheaf whose
sheafification is the associated module `(Ω_{X/Y})^a` of Stacks 03DU (4) — with `Γ(T, Ω_{T/Y})`.

This module records that identification *as a morphism of presheaves*: the restriction maps of
the pullback-sections presheaf of Stacks 03DS and of the relative-differentials presheaf are
both of the shape "the transpose of a morphism out of a pullback, read on global sections", and
the canonical maps of two stacked triangles compose, so the comparison is natural in `T`.

## Main definitions

* `AlgebraicGeometry.topAdjunctSectionsMap` is the map on global sections induced by the
  transpose of a morphism `g^*M ⟶ M'` across the pullback--pushforward adjunction.  It is the
  common shape of `AlgebraicGeometry.pullbackSectionsMap` and of
  `AlgebraicGeometry.differentialSectionsMap`.

## Main results

* `AlgebraicGeometry.topAdjunctSectionsMap_comm`: a commuting square of pullback comparisons
  gives a commuting square of the induced maps on global sections.
* `AlgebraicGeometry.pullbackSectionsMap_eq` and
  `AlgebraicGeometry.differentialSectionsMap_eq`: the two restriction maps in that shape.
* `AlgebraicGeometry.triangleDifferentialsMap_comp_sections`: **the comparison is natural.**
  Composing the canonical map `t^*Ω_{X/Y} ⟶ Ω_{T/Y}` on global sections with the canonical map of
  the triangle under a morphism `g` of schemes over `X` is the restriction map of the
  pullback-sections presheaf followed by the canonical map at the smaller object.
* `AlgebraicGeometry.topAdjunctSectionsMap_universalRelativeDerivation`: those canonical maps
  carry universal derivations to universal derivations.

## Implementation notes

The preimage of the top open under a morphism of schemes is the top open *definitionally* — that
is what makes `AlgebraicGeometry.Scheme.Hom.appTop` typecheck — so the `eqToHom` restriction that
`AlgebraicGeometry.pullbackSectionsMap` and `AlgebraicGeometry.differentialSectionsMap` carry is
the identity, and `AlgebraicGeometry.topAdjunctSectionsMap` omits it.  That is the one
simplification which keeps every proof below a chain of `Eq.trans`: with the restriction present,
the associativity rewrites needed to move it past a morphism of modules are rejected at the
transparency `rewrite` uses, the two spellings `Γ(g_*M', ⊤)` and `Γ(M', g^{-1}⊤)` of one object
being only definitionally equal.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map on
  relative differentials of a commutative square.
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), that map is an
  isomorphism for an étale source morphism.
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The map on global sections induced by a morphism `c : g^*M ⟶ M'`: its transpose across the
pullback--pushforward adjunction, read on global sections.  The target is `Γ(M', ⊤)` rather than
`Γ(M', g^{-1}⊤)` because the two are definitionally equal. -/
noncomputable def topAdjunctSectionsMap {T' T : Scheme.{u}} (g : T' ⟶ T) {M : T.Modules}
    {M' : T'.Modules} (c : (Scheme.Modules.pullback g).obj M ⟶ M') :
    Γ(M, ⊤) ⟶ Γ(M', ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M M' c).app ⊤

/-- **A commuting square of pullback comparisons induces a commuting square on global
sections.** -/
theorem topAdjunctSectionsMap_comm {T' T : Scheme.{u}} (g : T' ⟶ T) {M N : T.Modules}
    {M' N' : T'.Modules} (c : (Scheme.Modules.pullback g).obj M ⟶ M')
    (c' : (Scheme.Modules.pullback g).obj N ⟶ N') (u : M ⟶ N) (u' : M' ⟶ N')
    (h : (Scheme.Modules.pullback g).map u ≫ c' = c ≫ u') :
    topAdjunctSectionsMap g c ≫ u'.app ⊤ = u.app ⊤ ≫ topAdjunctSectionsMap g c' := by
  have key : u ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N N' c' =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M M' c ≫
        (Scheme.Modules.pushforward g).map u' := by
    rw [← (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left,
      ← (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right, h]
  exact (congrArg (fun z : M ⟶ (Scheme.Modules.pushforward g).obj N' =>
    Scheme.Modules.Hom.app z ⊤) key).symm

/-- Composing with the `eqToHom` restriction from the preimage of the top open to the top open
changes nothing: the two opens are definitionally equal, so the restriction is the identity. -/
private theorem comp_presheaf_map_top {T' T : Scheme.{u}} (g : T' ⟶ T) {M' : T'.Modules}
    {A : Ab.{u}} (a : A ⟶ Γ(M', g ⁻¹ᵁ ⊤)) (h : (⊤ : T'.Opens) = g ⁻¹ᵁ ⊤) :
    a ≫ M'.presheaf.map (eqToHom h).op = a :=
  Eq.trans
    (congrArg (fun z : Γ(M', g ⁻¹ᵁ ⊤) ⟶ Γ(M', g ⁻¹ᵁ ⊤) => a ≫ z)
      (M'.presheaf.map_id (op (g ⁻¹ᵁ ⊤))))
    (Category.comp_id a)

/-- The restriction map of the pullback-sections presheaf of Stacks 03DS is the map on global
sections induced by the canonical factorization comparison. -/
theorem pullbackSectionsMap_eq {S : Scheme.{u}} (F : S.Modules) {X Y : Over S} (g : X ⟶ Y) :
    pullbackSectionsMap F g =
      topAdjunctSectionsMap g.left
        (Scheme.Modules.pullbackFactorIso g.left Y.hom (Over.w g) F).hom :=
  comp_presheaf_map_top g.left
    (topAdjunctSectionsMap g.left
      (Scheme.Modules.pullbackFactorIso g.left Y.hom (Over.w g) F).hom) _

/-- The restriction map of the relative-differentials presheaf is the map on global sections
induced by the canonical map on relative differentials. -/
theorem differentialSectionsMap_eq {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y) :
    differentialSectionsMap g =
      topAdjunctSectionsMap g.left
        (Scheme.Hom.relativeDifferentialsMap g.left Y.hom X.hom (𝟙 S)
          (by simp [Over.w g])) :=
  comp_presheaf_map_top g.left
    (topAdjunctSectionsMap g.left
      (Scheme.Hom.relativeDifferentialsMap g.left Y.hom X.hom (𝟙 S) (by simp [Over.w g]))) _

/-- **The canonical map on relative differentials carries universal derivations to universal
derivations on global sections.**  This is the defining property of Stacks 01UV at the top
open. -/
theorem topAdjunctSectionsMap_universalRelativeDerivation {T T' Y : Scheme.{u}} (h : T' ⟶ T)
    (p : T ⟶ Y) (p' : T' ⟶ Y) (hcomm : h ≫ p = p' ≫ 𝟙 Y) (a : Γ(T, ⊤)) :
    topAdjunctSectionsMap h (Scheme.Hom.relativeDifferentialsMap h p p' (𝟙 Y) hcomm)
        ((Scheme.Hom.universalRelativeDerivation p).d a) =
      (Scheme.Hom.universalRelativeDerivation p').d ((h.app ⊤).hom a) :=
  Scheme.Hom.relativeDifferentialsMap_app_d (𝟙 Y) hcomm ⊤ a

/-- **The comparison of the two differentials presheaves is natural.**  For a morphism `g` of
schemes over `X` and `f : X ⟶ Y`, the canonical maps `t^*Ω_{X/Y} ⟶ Ω_{T/Y}` of Stacks 01UV
commute, on global sections, with the restriction map of the pullback-sections presheaf of
`Ω_{X/Y}` and the canonical map of the triangle under `g`. -/
theorem triangleDifferentialsMap_comp_sections {X Y : Scheme.{u}} (f : X ⟶ Y) {T T' : Over X}
    (g : T' ⟶ T) (hr : g.left ≫ T.hom ≫ f = T'.hom ≫ f) :
    pullbackSectionsMap (Scheme.Hom.relativeDifferentials f) g ≫
        (Scheme.Hom.triangleDifferentialsMap T'.hom f (T'.hom ≫ f) rfl).app ⊤ =
      (Scheme.Hom.triangleDifferentialsMap T.hom f (T.hom ≫ f) rfl).app ⊤ ≫
        topAdjunctSectionsMap g.left
          (Scheme.Hom.triangleDifferentialsMap g.left (T.hom ≫ f) (T'.hom ≫ f) hr) := by
  have h0 := Scheme.Hom.pullbackFactorIso_inv_comp_triangleDifferentialsMap f T.hom
    (T.hom ≫ f) rfl g.left (T'.hom ≫ f) (Over.w g) rfl hr
  have hsq : (Scheme.Modules.pullback g.left).map
        (Scheme.Hom.triangleDifferentialsMap T.hom f (T.hom ≫ f) rfl) ≫
        Scheme.Hom.triangleDifferentialsMap g.left (T.hom ≫ f) (T'.hom ≫ f) hr =
      (Scheme.Modules.pullbackFactorIso g.left T.hom (Over.w g)
          (Scheme.Hom.relativeDifferentials f)).hom ≫
        Scheme.Hom.triangleDifferentialsMap T'.hom f (T'.hom ≫ f) rfl :=
    Eq.trans
      ((Scheme.Modules.pullbackFactorIso g.left T.hom (Over.w g)
        (Scheme.Hom.relativeDifferentials f)).hom_inv_id_assoc _).symm
      (congrArg (fun z => (Scheme.Modules.pullbackFactorIso g.left T.hom (Over.w g)
        (Scheme.Hom.relativeDifferentials f)).hom ≫ z) h0)
  rw [pullbackSectionsMap_eq]
  exact topAdjunctSectionsMap_comm g.left _ _ _ _ hsq

end AlgebraicGeometry

end
