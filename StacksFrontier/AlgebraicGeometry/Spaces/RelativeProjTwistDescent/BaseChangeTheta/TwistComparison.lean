module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.PullbackDescended
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.QuadrupleLiesOver

/-!
# The comparison of twists along the base change, and `θ_n`

The comparison `y^*𝒪_{U ×_X P}(n) ≅ 𝒪_{V ×_{X'} P'}(n)` of twists along a morphism lying over `k`
and `h`, its two cocycle conditions and its compatibility with the transitions of the twists, and
the descended isomorphism `θ_n : h^*𝒪_P(n) ≅ 𝒪_{P'}(n)` of Stacks 085C
(`RelativeProjSituation.baseChangeTwistModuleIso`).
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-! ### The comparison of twists along the base change -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m}) {X' : AlgebraicSpaces s.site s.base s.containsBase}
  (g : X' ⟶ s.space)

/-- The morphism `Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)` lies over `g`. -/
theorem relativeProjBaseChangeHom_comp_relativeProjπ :
    s.relativeProjBaseChangeHom g ≫ s.relativeProjπ = (s.pullback g).relativeProjπ ≫ g.hom :=
  (s.isPullback_relativeProjBaseChangeHom g).w

/-- **The comparison of the restricted algebras along `k` and `g`**: for scheme points `u` of `X`
and `v` of `X'` with `u ∘ k = g ∘ v`, the composite `v^*(g^*𝒜) ≅ (g v)^*𝒜 ≅ k^*(u^*𝒜)` of
`AlgebraicGeometry.Space.pullbackPointHom` and the restriction along `k`. -/
abbrev baseChangeAlgebraHom {U V : BigFppfOver s.site s.base s.containsBase} (k : V ⟶ U)
    (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ X'.1)
    (hv : yoneda.map k ≫ u = v ≫ g.hom) :=
  GradedAlgebraRestriction.ComapHom.compRestrict (Â := s.shrink.pointAlgebra)
    (Â' := (s.pullback g).shrink.pointAlgebra) (ρ₁ := s.quadrupleRestriction)
    (ρ₁' := (s.pullback g).quadrupleRestriction) (s.pullbackComapHom g) k u v hv

/-- The comparison of the restricted algebras along `k` and `g` is invertible in every degree. -/
theorem isIso_baseChangeAlgebraHom_app {U V : BigFppfOver s.site s.base s.containsBase}
    (k : V ⟶ U) (u : yoneda.obj U ⟶ s.space.1) (v : yoneda.obj V ⟶ X'.1)
    (hv : yoneda.map k ≫ u = v ≫ g.hom) (n : ℤ) :
    IsIso ((s.baseChangeAlgebraHom g k u v hv).app n) :=
  GradedAlgebraRestriction.ComapHom.isIso_compRestrict_app _ _ _ _ _ n

/-- **A morphism `V ×_{X'} P' ⟶ U ×_X P` lying over `k` and `h` is, on schemes, the
identification `Proj_V(v^*g^*𝒜) ≅ Proj_V(k^*u^*𝒜)` followed by the base-change morphism of
Tag 01O3.** -/
theorem toScheme_map_eq_of_liesOverAlong {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    {y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y =
      (relativeProjCongr (A₁ := (s.pullback g).shrink.pointAlgebra V v)
        (A₂ := (s.shrink.pointAlgebra U u).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
        (s.baseChangeAlgebraHom g k u v hv) (s.isIso_baseChangeAlgebraHom_app g k u v hv)).hom ≫
      baseChangeHom (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k) :=
  GradedAlgebraRestriction.ComapHom.toScheme_map_eq_of_liesOverAlong (Â := s.shrink.pointAlgebra)
    (Â' := (s.pullback g).shrink.pointAlgebra) (ρ₁ := s.quadrupleRestriction)
    (ρ₁' := (s.pullback g).quadrupleRestriction) (e₁ := s.pullbackComapHom g)
    (hc := s.shrink.contains_relativeProj_pointAlgebra)
    (hc' := (s.pullback g).shrink.contains_relativeProj_pointAlgebra)
    (hX := s.space.property.isSheaf) (hX' := X'.property.isSheaf) hv hy

/-- A morphism of base changes lying over `k` and `h` commutes with the structure morphisms of the
two relative homogeneous spectra. -/
theorem toScheme_map_comp_toBase_of_liesOverAlong
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {k : V ⟶ U}
    {y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫
        (relativeProj (s.shrink.pointAlgebra U u)).toBase =
      (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).toBase ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k :=
  GradedAlgebraRestriction.ComapHom.toScheme_map_comp_toBase_of_liesOverAlong
    (Â := s.shrink.pointAlgebra) (Â' := (s.pullback g).shrink.pointAlgebra)
    (ρ₁ := s.quadrupleRestriction) (ρ₁' := (s.pullback g).quadrupleRestriction)
    (e₁ := s.pullbackComapHom g) (hc := s.shrink.contains_relativeProj_pointAlgebra)
    (hc' := (s.pullback g).shrink.contains_relativeProj_pointAlgebra)
    (hX := s.space.property.isSheaf) (hX' := X'.property.isSheaf) hy

/-- A morphism of base changes of `P'` and `P`, read on the relative homogeneous spectra, commutes
with `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
theorem map_comp_toRelativeProj_baseChange {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1}
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫ s.toRelativeProj U u =
      (s.pullback g).toRelativeProj V v ≫
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
          (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme ⟶
            (relativeProj (s.shrink.pointAlgebra U u)).scheme) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The comparison of the twists `𝒪(n)` along a morphism of base changes lying over `k` and
`h`**, as an isomorphism of sheaves of modules: the degree-`n` piece of Tag 01O3's `θ` along the
identification of the restricted algebras and the base-change morphism, transported along the
squares of `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
def baseChangeTwistSheafIso {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (n : ℤ) :
    @Iso (SheafOfModules.{u} ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        ((s.pullback g).relativeProjPoints.fibre V v)).ringCatSheaf) _
      (quasicoherentPullbackObj s.site s.base s.containsBase y (s.twistPieceQcoh U u n)).obj
      ((s.pullback g).twistPieceQcoh V v n).obj :=
  pullbackSheafIsoOfSquare (s.toRelativeProj U u)
    ((s.pullback g).toRelativeProj V v :
      (BigFppfOver.toScheme s.site s.base s.containsBase).obj
          ((s.pullback g).relativeProjPoints.fibre V v) ⟶
        (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (s.map_comp_toRelativeProj_baseChange g y)
    (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
      (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
        (s.isIso_baseChangeAlgebraHom_app g k u v hv)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.toScheme_map_eq_of_liesOverAlong g hv hy)) n)

/-- **The comparison of the twists `𝒪(n)` along a morphism of base changes lying over `k` and
`h`**, `y^*𝒪_{U ×_X P}(n) ≅ 𝒪_{V ×_{X'} P'}(n)`, as an isomorphism of quasi-coherent modules. -/
def baseChangeTwistPieceComparison {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase y (s.twistPieceQcoh U u n) ≅
      (s.pullback g).twistPieceQcoh V v n where
  hom := ⟨(s.baseChangeTwistSheafIso g k hv y hy n).hom⟩
  inv := ⟨(s.baseChangeTwistSheafIso g k hv y hy n).inv⟩
  hom_inv_id := ObjectProperty.hom_ext _ (s.baseChangeTwistSheafIso g k hv y hy n).hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ (s.baseChangeTwistSheafIso g k hv y hy n).inv_hom_id

/-- The comparison of twists depends on the morphism of base changes only through its value. -/
theorem quasicoherentPullbackEqToHom_comp_baseChangeTwistPieceComparison_hom
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {k₁ k₂ : V ⟶ U}
    {hv₁ : yoneda.map k₁ ≫ u = v ≫ g.hom} {hv₂ : yoneda.map k₂ ≫ u = v ≫ g.hom}
    {y₁ y₂ : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    {hy₁ : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y₁ k₁}
    {hy₂ : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y₂ k₂} (e : y₁ = y₂) (hk : k₁ = k₂) (n : ℤ) :
    quasicoherentPullbackEqToHom s.site s.base s.containsBase e (s.twistPieceQcoh U u n) ≫
        (s.baseChangeTwistPieceComparison g k₂ hv₂ y₂ hy₂ n).hom =
      (s.baseChangeTwistPieceComparison g k₁ hv₁ y₁ hy₁ n).hom := by
  subst e hk
  exact (congrArg (· ≫ _) (quasicoherentPullbackEqToHom_rfl s.site s.base s.containsBase _)).trans
    (Category.id_comp _)

/-! ### The two cocycle conditions -/

/-- **The comparison along `y ≫ x`, for `x` a morphism of base changes of `P` lying over `k₀`**,
is the comparison of twists of `P` along `x`, pulled back along `y` and contracted, followed by
the comparison along `y`. -/
theorem baseChangeTwistSheafIso_comp_liesOver {U V W : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {w : yoneda.obj W ⟶ s.space.1}
    (k : V ⟶ U) (k₀ : U ⟶ W) (hv : yoneda.map k ≫ u = v ≫ g.hom) (hu : yoneda.map k₀ ≫ w = u)
    (hv' : yoneda.map (k ≫ k₀) ≫ w = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (x : s.relativeProjPoints.fibre U u ⟶ s.relativeProjPoints.fibre W w)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (hx : s.relativeProjPoints.LiesOver x k₀) (n : ℤ) :
    (s.baseChangeTwistSheafIso g (k ≫ k₀) hv' (y ≫ x) (hy.comp_liesOver hx) n).hom =
      (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp y x)).hom.app
          ((Scheme.Modules.pullback (s.toRelativeProj W w)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W w)).piece n)) ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map x)).inv.app
          ((Scheme.Modules.pullback (s.toRelativeProj W w)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W w)).piece n)) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
            (s.twistPieceSheafIso k₀ hu x hx n).hom ≫
            (s.baseChangeTwistSheafIso g k hv y hy n).hom := by
  have B4 := congrBaseChangeTwistIso_comp (s.shrink.pointAlgebra W w)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k₀)
    (A₁ := s.shrink.pointAlgebra U u) (s.quadrupleRestriction.restrict k₀ w u hu)
    (s.quadrupleRestriction.isIso_restrict_app k₀ w u hu)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map x)
    (s.toScheme_map_eq_of_liesOver hu hx)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (k ≫ k₀))
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map_comp k k₀).symm
    (A'' := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
    (s.isIso_baseChangeAlgebraHom_app g k u v hv) (s.baseChangeAlgebraHom g (k ≫ k₀) w v hv')
    (s.isIso_baseChangeAlgebraHom_app g (k ≫ k₀) w v hv')
    (GradedAlgebraRestriction.ComapHom.congrHom_compRestrict_comp (Â := s.shrink.pointAlgebra)
      (Â' := (s.pullback g).shrink.pointAlgebra) (ρ₁ := s.quadrupleRestriction)
      (ρ₁' := (s.pullback g).quadrupleRestriction) (s.pullbackComapHom g) k k₀ hv hu hv')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (s.toScheme_map_eq_of_liesOverAlong g hv hy)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y ≫ x))
    (s.toScheme_map_eq_of_liesOverAlong g hv' (hy.comp_liesOver hx))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp y x)
    (s.toScheme_map_comp_toBase_of_liesOver hu hx)
    (s.toScheme_map_comp_toBase_of_liesOverAlong g hy)
  have e2 := gradedPieceIso_hom_eq_of_eq_trans _ _ _ _ n _ _ _ B4
  have key := pullbackSheafIsoOfSquare_comp (s.toRelativeProj W w) (s.toRelativeProj U u)
    ((s.pullback g).toRelativeProj V v :
      (BigFppfOver.toScheme s.site s.base s.containsBase).obj
          ((s.pullback g).relativeProjPoints.fibre V v) ⟶
        (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map x)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (y ≫ x))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _) _ _ _
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _)
    (s.map_comp_toRelativeProj x) (s.map_comp_toRelativeProj_baseChange g y)
    (s.map_comp_toRelativeProj_baseChange g (y ≫ x)) _ _ _ e2
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · refine congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) ?_ ?_))
    · rfl
    · rfl

/-- **The comparison along `x' ≫ y`, for `x'` a morphism of base changes of `P'` lying over `k'`**,
is the comparison along `y`, pulled back along `x'` and contracted, followed by the comparison of
twists of `P'` along `x'`. -/
theorem baseChangeTwistSheafIso_liesOver_comp {U V V' : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {v' : yoneda.obj V' ⟶ X'.1}
    (k : V ⟶ U) (k' : V' ⟶ V) (hv : yoneda.map k ≫ u = v ≫ g.hom) (hw : yoneda.map k' ≫ v = v')
    (hv' : yoneda.map (k' ≫ k) ≫ u = v' ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (x' : (s.pullback g).relativeProjPoints.fibre V' v' ⟶
      (s.pullback g).relativeProjPoints.fibre V v)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k)
    (hx' : (s.pullback g).relativeProjPoints.LiesOver x' k') (n : ℤ) :
    (s.baseChangeTwistSheafIso g (k' ≫ k) hv' (x' ≫ y) (hx'.comp_liesOverAlong hy) n).hom =
      (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp x' y)).hom.app
          ((Scheme.Modules.pullback (s.toRelativeProj U u)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)).piece n)) ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map x')
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).inv.app
          ((Scheme.Modules.pullback (s.toRelativeProj U u)).obj
            ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)).piece n)) ≫
          (Scheme.Modules.pullback
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map x')).map
            (s.baseChangeTwistSheafIso g k hv y hy n).hom ≫
            ((s.pullback g).twistPieceSheafIso k' hw x' hx' n).hom := by
  have B4 := congrBaseChangeTwistIso_comp (s.shrink.pointAlgebra U u)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
    (s.isIso_baseChangeAlgebraHom_app g k u v hv)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (s.toScheme_map_eq_of_liesOverAlong g hv hy)
    ((BigFppfOver.toScheme (s.pullback g).shrink.site (s.pullback g).shrink.base
      (s.pullback g).shrink.containsBase).map k')
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (k' ≫ k))
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map_comp k' k).symm
    (A'' := (s.pullback g).shrink.pointAlgebra V' v')
    ((s.pullback g).quadrupleRestriction.restrict k' v v' hw)
    ((s.pullback g).quadrupleRestriction.isIso_restrict_app k' v v' hw)
    (s.baseChangeAlgebraHom g (k' ≫ k) u v' hv')
    (s.isIso_baseChangeAlgebraHom_app g (k' ≫ k) u v' hv')
    (GradedAlgebraRestriction.ComapHom.congrHom_restrict_comp_compRestrict
      (Â := s.shrink.pointAlgebra) (Â' := (s.pullback g).shrink.pointAlgebra)
      (ρ₁ := s.quadrupleRestriction) (ρ₁' := (s.pullback g).quadrupleRestriction)
      (s.pullbackComapHom g) k k' hv hw hv')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map x')
    ((s.pullback g).toScheme_map_eq_of_liesOver hw hx')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (x' ≫ y))
    (s.toScheme_map_eq_of_liesOverAlong g hv' (hx'.comp_liesOverAlong hy))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp x' y)
    (s.toScheme_map_comp_toBase_of_liesOverAlong g hy)
    ((s.pullback g).toScheme_map_comp_toBase_of_liesOver hw hx')
  have e2 := gradedPieceIso_hom_eq_of_eq_trans _ _ _ _ n _ _ _ B4
  have key := pullbackSheafIsoOfSquare_comp (s.toRelativeProj U u)
    ((s.pullback g).toRelativeProj V v)
    ((s.pullback g).toRelativeProj V' v')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map x')
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (x' ≫ y))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _) _ _ _
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _)
    (s.map_comp_toRelativeProj_baseChange g y) ((s.pullback g).map_comp_toRelativeProj x')
    (s.map_comp_toRelativeProj_baseChange g (x' ≫ y)) _ _ _ e2
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · refine congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) ?_ ?_))
    · rfl
    · rfl

/-! ### The comparison carries the transition of the twists of `P` to that of `P'` -/

/-- The telescoping behind `schemePairTransition_twistPieceComparison_baseChange`, at
variables. -/
private theorem pairTransition_telescope {C : Type*} [Category C]
    {Pt Pt2 Pt3 Ps Ps2 Ps3 Qt Qs E : C} (cHt : Pt ≅ Pt2) (cHs : Ps ≅ Ps2) (eT : Pt2 ⟶ Pt3)
    (eS : Ps3 ⟶ Ps2) (ρ : Pt3 ⟶ Ps3) (Θt2 : Pt2 ≅ E) (Θt3 : Pt3 ≅ E) (Θs2 : Ps2 ≅ E)
    (Θs3 : Ps3 ≅ E) (mapT : Pt ⟶ Qt) (mapS : Ps ⟶ Qs) (Tt : Qt ≅ E) (Ts : Qs ≅ E)
    (hA : ρ = Θt3.hom ≫ Θs3.inv) (hB : Θt2.hom = cHt.inv ≫ mapT ≫ Tt.hom)
    (hB' : Θs2.hom = cHs.inv ≫ mapS ≫ Ts.hom) (hC : eT ≫ Θt3.hom = Θt2.hom)
    (hC' : eS ≫ Θs2.hom = Θs3.hom) :
    (cHt.hom ≫ (eT ≫ ρ ≫ eS) ≫ cHs.inv) ≫ mapS = mapT ≫ Tt.hom ≫ Ts.inv := by
  have h1 : Θs3.inv ≫ eS = Θs2.inv := by
    rw [← cancel_epi Θs3.hom, Iso.hom_inv_id_assoc, ← hC', Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 : Θs2.inv ≫ cHs.inv ≫ mapS = Ts.inv := by
    rw [← cancel_epi Θs2.hom, Iso.hom_inv_id_assoc, hB']
    simp
  have h3 : cHt.hom ≫ Θt2.hom = mapT ≫ Tt.hom := by
    rw [hB, Iso.hom_inv_id_assoc]
  calc (cHt.hom ≫ (eT ≫ ρ ≫ eS) ≫ cHs.inv) ≫ mapS
      = cHt.hom ≫ (eT ≫ Θt3.hom) ≫ (Θs3.inv ≫ eS) ≫ cHs.inv ≫ mapS := by
        rw [hA]
        simp only [Category.assoc]
    _ = (cHt.hom ≫ Θt2.hom) ≫ Θs2.inv ≫ cHs.inv ≫ mapS := by
        rw [hC, h1]
        simp only [Category.assoc]
    _ = mapT ≫ Tt.hom ≫ Ts.inv := by rw [h3, h2, Category.assoc]

/-- **The comparison of twists along a morphism of the presenting schemes carries the pulled-back
transition of the twists of `P` to the transition of the twists of `P'`**, at variables: for
projections `t', s'` of `R ×_X P ⇉ U ×_X P` and `t'', s''` of `R'' ×_{X'} P' ⇉ U'' ×_{X'} P'`
lying over `kt, ks` and `kt'', ks''`, and morphisms `yU`, `yR` lying over `ℓ`, `ℓR` and `h`
compatible with the projections. -/
theorem schemePairTransition_twistPieceComparison_baseChange
    {U R U'' R'' : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {r : yoneda.obj R ⟶ s.space.1}
    {u'' : yoneda.obj U'' ⟶ X'.1} {r'' : yoneda.obj R'' ⟶ X'.1}
    (kt ks : R ⟶ U) (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
    (tR sR : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
    (htR : s.relativeProjPoints.LiesOver tR kt) (hsR : s.relativeProjPoints.LiesOver sR ks)
    (kt'' ks'' : R'' ⟶ U'') (hrt'' : yoneda.map kt'' ≫ u'' = r'')
    (hrs'' : yoneda.map ks'' ≫ u'' = r'')
    (tR'' sR'' : (s.pullback g).relativeProjPoints.fibre R'' r'' ⟶
      (s.pullback g).relativeProjPoints.fibre U'' u'')
    (htR'' : (s.pullback g).relativeProjPoints.LiesOver tR'' kt'')
    (hsR'' : (s.pullback g).relativeProjPoints.LiesOver sR'' ks'')
    (ℓ : U'' ⟶ U) (hℓ : yoneda.map ℓ ≫ u = u'' ≫ g.hom)
    (yU : (s.pullback g).relativeProjPoints.fibre U'' u'' ⟶ s.relativeProjPoints.fibre U u)
    (hyU : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yU ℓ)
    (ℓR : R'' ⟶ R) (hℓR : yoneda.map ℓR ≫ r = r'' ≫ g.hom)
    (yR : (s.pullback g).relativeProjPoints.fibre R'' r'' ⟶ s.relativeProjPoints.fibre R r)
    (hyR : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yR ℓR)
    (hta : tR'' ≫ yU = yR ≫ tR) (hsb : yR ≫ sR = sR'' ≫ yU)
    (hbt : kt'' ≫ ℓ = ℓR ≫ kt) (hbs : ℓR ≫ ks = ks'' ≫ ℓ) (n : ℤ) :
    schemePairTransition s.site s.base s.containsBase yU yR hta hsb (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt tR htR n).hom ≫
          (s.twistPieceComparison ks hrs sR hsR n).inv) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase sR''
        (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase tR''
        (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom ≫
      ((s.pullback g).twistPieceComparison kt'' hrt'' tR'' htR'' n).hom ≫
        ((s.pullback g).twistPieceComparison ks'' hrs'' sR'' hsR'' n).inv := by
  have hcomp : ∀ (k : R ⟶ U) (hrk : yoneda.map k ≫ u = r),
      yoneda.map (ℓR ≫ k) ≫ u = r'' ≫ g.hom := fun k hrk => by
    rw [Functor.map_comp, Category.assoc, hrk, hℓR]
  have hcomp'' : ∀ (k : R'' ⟶ U'') (hrk : yoneda.map k ≫ u'' = r''),
      yoneda.map (k ≫ ℓ) ≫ u = r'' ≫ g.hom := fun k hrk => by
    rw [Functor.map_comp, Category.assoc, hℓ, ← Category.assoc, hrk]
  have pt := hcomp kt hrt
  have ps := hcomp ks hrs
  have pt'' := hcomp'' kt'' hrt''
  have ps'' := hcomp'' ks'' hrs''
  have hA := schemeTransitionReindex_eq_of_comp_of_hom_eq s.site s.base s.containsBase tR sR
    (s.twistPieceQcoh U u n) yR (s.twistPieceComparison kt hrt tR htR n)
    (s.twistPieceComparison ks hrs sR hsR n) (s.baseChangeTwistPieceComparison g ℓR hℓR yR hyR n)
    (s.baseChangeTwistPieceComparison g (ℓR ≫ kt) pt (yR ≫ tR) (hyR.comp_liesOver htR) n)
    (s.baseChangeTwistPieceComparison g (ℓR ≫ ks) ps (yR ≫ sR) (hyR.comp_liesOver hsR) n)
    (s.twistPieceSheafIso kt hrt tR htR n).hom rfl (s.twistPieceSheafIso ks hrs sR hsR n).hom rfl
    (s.baseChangeTwistSheafIso g ℓR hℓR yR hyR n).hom rfl
    (s.baseChangeTwistSheafIso g (ℓR ≫ kt) pt (yR ≫ tR) (hyR.comp_liesOver htR) n).hom rfl
    (s.baseChangeTwistSheafIso g (ℓR ≫ ks) ps (yR ≫ sR) (hyR.comp_liesOver hsR) n).hom rfl
    (s.baseChangeTwistSheafIso_comp_liesOver g ℓR kt hℓR hrt pt yR tR hyR htR n)
    (s.baseChangeTwistSheafIso_comp_liesOver g ℓR ks hℓR hrs ps yR sR hyR hsR n)
  have hB : ∀ (k : R'' ⟶ U'') (hrk : yoneda.map k ≫ u'' = r'')
      (t : (s.pullback g).relativeProjPoints.fibre R'' r'' ⟶
        (s.pullback g).relativeProjPoints.fibre U'' u'')
      (ht : (s.pullback g).relativeProjPoints.LiesOver t k),
      (s.baseChangeTwistPieceComparison g (k ≫ ℓ) (hcomp'' k hrk) (t ≫ yU)
        (ht.comp_liesOverAlong hyU) n).hom =
      (quasicoherentPullbackCompIso s.site s.base s.containsBase t yU
          (s.twistPieceQcoh U u n)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase t
          (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom ≫
          ((s.pullback g).twistPieceComparison k hrk t ht n).hom := fun k hrk t ht =>
    ObjectProperty.hom_ext _
      ((s.baseChangeTwistSheafIso_liesOver_comp g ℓ k hℓ hrk (hcomp'' k hrk) yU t hyU ht
        n).trans
        ((congrArg (· ≫ _) (rfl : (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp t yU)).hom.app
            ((Scheme.Modules.pullback (s.toRelativeProj U u)).obj
              ((Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)).piece n)) = 𝟙 _)).trans
          (Category.id_comp _)))
  have hC := s.quasicoherentPullbackEqToHom_comp_baseChangeTwistPieceComparison_hom g
    (hv₁ := pt'') (hv₂ := pt) (hy₁ := htR''.comp_liesOverAlong hyU)
    (hy₂ := hyR.comp_liesOver htR) hta hbt n
  have hC' := s.quasicoherentPullbackEqToHom_comp_baseChangeTwistPieceComparison_hom g
    (hv₁ := ps) (hv₂ := ps'') (hy₁ := hyR.comp_liesOver hsR)
    (hy₂ := hsR''.comp_liesOverAlong hyU) hsb hbs n
  exact pairTransition_telescope
    (quasicoherentPullbackCompIso s.site s.base s.containsBase tR'' yU (s.twistPieceQcoh U u n))
    (quasicoherentPullbackCompIso s.site s.base s.containsBase sR'' yU (s.twistPieceQcoh U u n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hta (s.twistPieceQcoh U u n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hsb (s.twistPieceQcoh U u n))
    (schemeTransitionReindex s.site s.base s.containsBase tR sR (s.twistPieceQcoh U u n)
      ((s.twistPieceComparison kt hrt tR htR n).hom ≫
        (s.twistPieceComparison ks hrs sR hsR n).inv) yR)
    (s.baseChangeTwistPieceComparison g (kt'' ≫ ℓ) pt'' (tR'' ≫ yU)
      (htR''.comp_liesOverAlong hyU) n)
    (s.baseChangeTwistPieceComparison g (ℓR ≫ kt) pt (yR ≫ tR) (hyR.comp_liesOver htR) n)
    (s.baseChangeTwistPieceComparison g (ks'' ≫ ℓ) ps'' (sR'' ≫ yU)
      (hsR''.comp_liesOverAlong hyU) n)
    (s.baseChangeTwistPieceComparison g (ℓR ≫ ks) ps (yR ≫ sR) (hyR.comp_liesOver hsR) n)
    (quasicoherentPullbackMap s.site s.base s.containsBase tR''
      (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom)
    (quasicoherentPullbackMap s.site s.base s.containsBase sR''
      (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom)
    ((s.pullback g).twistPieceComparison kt'' hrt'' tR'' htR'' n)
    ((s.pullback g).twistPieceComparison ks'' hrs'' sR'' hsR'' n) hA (hB _ _ _ _)
    (hB _ _ _ _) hC hC'

/-- `schemePairTransition_twistPieceComparison_baseChange` with the base changes of `P'` typed
over the site of `X` and the two transitions given as morphisms equal to the composites of the
comparisons of twists: the form in which it is instantiated at the presentations. -/
theorem schemePairTransition_baseChangeTwistPieceComparison_of_eq
    {U R U'' R'' : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {r : yoneda.obj R ⟶ s.space.1}
    {u'' : yoneda.obj U'' ⟶ X'.1} {r'' : yoneda.obj R'' ⟶ X'.1}
    (kt ks : R ⟶ U) (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
    (tR sR : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
    (htR : s.relativeProjPoints.LiesOver tR kt) (hsR : s.relativeProjPoints.LiesOver sR ks)
    (kt'' ks'' : R'' ⟶ U'') (hrt'' : yoneda.map kt'' ≫ u'' = r'')
    (hrs'' : yoneda.map ks'' ≫ u'' = r'')
    (tR'' sR'' : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := X'.obj) (s.pullback g).relativeProjPoints R'' r'' ⟶
      RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase) (X := X'.obj)
        (s.pullback g).relativeProjPoints U'' u'')
    (htR'' : (s.pullback g).relativeProjPoints.LiesOver tR'' kt'')
    (hsR'' : (s.pullback g).relativeProjPoints.LiesOver sR'' ks'')
    (ℓ : U'' ⟶ U) (hℓ : yoneda.map ℓ ≫ u = u'' ≫ g.hom)
    (yU : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase) (X := X'.obj)
        (s.pullback g).relativeProjPoints U'' u'' ⟶ s.relativeProjPoints.fibre U u)
    (hyU : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yU ℓ)
    (ℓR : R'' ⟶ R) (hℓR : yoneda.map ℓR ≫ r = r'' ≫ g.hom)
    (yR : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase) (X := X'.obj)
        (s.pullback g).relativeProjPoints R'' r'' ⟶ s.relativeProjPoints.fibre R r)
    (hyR : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yR ℓR)
    (hta : tR'' ≫ yU = yR ≫ tR) (hsb : yR ≫ sR = sR'' ≫ yU)
    (hbt : kt'' ≫ ℓ = ℓR ≫ kt) (hbs : ℓR ≫ ks = ks'' ≫ ℓ) (n : ℤ)
    (τ : quasicoherentPullbackObj s.site s.base s.containsBase tR (s.twistPieceQcoh U u n) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase sR (s.twistPieceQcoh U u n))
    (hτ : τ = (s.twistPieceComparison kt hrt tR htR n).hom ≫
      (s.twistPieceComparison ks hrs sR hsR n).inv)
    (τ'' : quasicoherentPullbackObj s.site s.base s.containsBase tR''
        ((s.pullback g).twistPieceQcoh U'' u'' n) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase sR''
        ((s.pullback g).twistPieceQcoh U'' u'' n))
    (hτ'' : τ'' = ((s.pullback g).twistPieceComparison kt'' hrt'' tR'' htR'' n).hom ≫
        ((s.pullback g).twistPieceComparison ks'' hrs'' sR'' hsR'' n).inv) :
    schemePairTransition s.site s.base s.containsBase yU yR hta hsb (s.twistPieceQcoh U u n) τ ≫
      quasicoherentPullbackMap s.site s.base s.containsBase sR''
        (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase tR''
        (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n).hom ≫ τ'' := by
  subst hτ hτ''
  exact s.schemePairTransition_twistPieceComparison_baseChange g kt ks hrt hrs tR sR htR hsR kt''
    ks'' hrt'' hrs'' tR'' sR'' htR'' hsR'' ℓ hℓ yU hyU ℓR hℓR yR hyR hta hsb hbt hbs n

/-! ### `θ_n` on the presentations -/

section Theta

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (Px' : Presentation s.site s.base s.containsBase X'.obj X'.property)
  (ℓ : Px'.U ⟶ Px.U) (hℓ : yoneda.map ℓ ≫ Px.toSpace = Px'.toSpace ≫ g.hom)
  (ℓR : Px'.R ⟶ Px.R) (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ)

/-- **The morphism `h : Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)` of Stacks 085C**, as a morphism of algebraic
spaces. -/
abbrev relativeProjBaseChangeSpaceHom :
    (⟨(s.pullback g).relativeProjFunctor, (s.pullback g).isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶
      ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :=
  ObjectProperty.homMk (s.relativeProjBaseChangeHom g)

include hℓ hℓt in
/-- The morphism of the relations lies over `g` on the points of the relations. -/
theorem map_relation_comp_relationPoint :
    yoneda.map ℓR ≫ RelativeProjPoints.relationPoint Px =
      RelativeProjPoints.relationPoint Px' ≫ g.hom := by
  change yoneda.map ℓR ≫ yoneda.map Px.target ≫ Px.toSpace =
    (yoneda.map Px'.target ≫ Px'.toSpace) ≫ g.hom
  rw [← Category.assoc, ← Functor.map_comp, hℓt, Functor.map_comp, Category.assoc, hℓ,
    Category.assoc]

/-- **The morphism `U' ×_{X'} P' ⟶ U ×_X P` of the presenting schemes** induced by `ℓ` and `h`. -/
abbrev chartBaseChangeMap :
    (s.pullback g).relativeProjPoints.fibre Px'.U Px'.toSpace ⟶
      s.relativeProjPoints.fibre Px.U Px.toSpace :=
  RelativeProjPoints.fibreMapAlong _ _ _ (s.relativeProjBaseChangeHom_comp_relativeProjπ g)
    Px.toSpace Px'.toSpace ℓ hℓ

/-- **The morphism `R' ×_{X'} P' ⟶ R ×_X P` of the relation schemes** induced by `ℓR` and `h`. -/
abbrev relationBaseChangeMap :
    (s.pullback g).relativeProjPoints.fibre Px'.R (RelativeProjPoints.relationPoint Px') ⟶
      s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px) :=
  RelativeProjPoints.fibreMapAlong _ _ _ (s.relativeProjBaseChangeHom_comp_relativeProjπ g)
    (RelativeProjPoints.relationPoint Px) (RelativeProjPoints.relationPoint Px') ℓR
    (s.map_relation_comp_relationPoint g Px Px' ℓ hℓ ℓR hℓt)

/-- The morphism of the presenting schemes lies over `ℓ` and `h`. -/
theorem liesOverAlong_chartBaseChangeMap :
    (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) (s.chartBaseChangeMap g Px Px' ℓ hℓ) ℓ :=
  RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _

/-- The morphism of the relation schemes lies over `ℓR` and `h`. -/
theorem liesOverAlong_relationBaseChangeMap :
    (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) (s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt) ℓR :=
  RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _

/-- The morphisms of the presenting schemes commute with the target projections. -/
theorem spaceTarget_comp_chartBaseChangeMap :
    ((s.pullback g).relativeProjPoints.spacePresentation Px'
        (s.pullback g).isAlgebraicSpace_relativeProjFunctor).target ≫
        s.chartBaseChangeMap g Px Px' ℓ hℓ =
      s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt ≫
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor).target :=
  RelativeProjPoints.presentationTarget_comp_fibreMapAlong
    (s.relativeProjBaseChangeHom_comp_relativeProjπ g) Px Px'
    s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor ℓ hℓ
    ℓR (s.map_relation_comp_relationPoint g Px Px' ℓ hℓ ℓR hℓt) hℓt

/-- The atlases of the two presentations are compatible with `h`. -/
theorem presentationAtlas_comp_relativeProjBaseChangeSpaceHom :
    presentationAtlas ((s.pullback g).relativeProjPoints.spacePresentation Px'
        (s.pullback g).isAlgebraicSpace_relativeProjFunctor) ≫
        s.relativeProjBaseChangeSpaceHom g =
      representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap g Px Px' ℓ hℓ) ≫
        presentationAtlas (s.relativeProjPoints.spacePresentation Px
          s.isAlgebraicSpace_relativeProjFunctor) :=
  ObjectProperty.hom_ext _ (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ).2.symm

/-- **The comparison of the twists on the presenting schemes**,
`(U' ×_{X'} P' ⟶ U ×_X P)^*𝒪(n) ≅ 𝒪(n)`. -/
abbrev chartTwistComparison (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.twistPieceQcoh Px.U Px.toSpace n) ≅
      (s.pullback g).twistPieceQcoh Px'.U Px'.toSpace n :=
  s.baseChangeTwistPieceComparison g ℓ hℓ _ (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) n

/-- The identification on the atlas of `P'` of the inverse image `h^*𝒪_P(n)` with the twist
`𝒪(n)` on `U' ×_{X'} P'`. -/
abbrev baseChangeTwistChartIso (n : ℤ) :=
  presentationPullbackChartIso ((s.pullback g).relativeProjPoints.spacePresentation Px'
      (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjBaseChangeSpaceHom g) (s.chartBaseChangeMap g Px Px' ℓ hℓ)
    (s.presentationAtlas_comp_relativeProjBaseChangeSpaceHom g Px Px' ℓ hℓ) (s.twistModule Px n)
    (s.twistModuleChartIso Px n) (s.chartTwistComparison g Px Px' ℓ hℓ n)

/-- The inverse image `h^*𝒪_P(n)`, as a quasi-coherent `𝒪_{P'}`-module. -/
abbrev pullbackTwistModule (n : ℤ) :
    QuasicoherentSheaves.{u, u} s.site s.base s.containsBase (s.pullback g).relativeProjFunctor
      (s.pullback g).isAlgebraicSpace_relativeProjFunctor :=
  ⟨(modulePullback s.site s.base s.containsBase (s.relativeProjBaseChangeSpaceHom g)).obj
      (s.twistModule Px n).obj,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase _ _
      (s.isQuasicoherentOnSite_twistModule Px n)⟩


/-- **The comparison of twists along a morphism of the presenting schemes carries the transition
of the twists of `P` to that of `P'`** (the compatibility of Stacks 03M3 for `θ_n`), for any
morphisms `U' ×_{X'} P' ⟶ U ×_X P` and `R' ×_{X'} P' ⟶ R ×_X P` lying over `ℓ`, `ℓR` and `h`. -/
theorem pullbackTransitionCompatible_twistTransition (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ)
    (yU : (s.pullback g).relativeProjPoints.fibre Px'.U Px'.toSpace ⟶
      s.relativeProjPoints.fibre Px.U Px.toSpace)
    (hyU : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yU ℓ)
    (yR : (s.pullback g).relativeProjPoints.fibre Px'.R (RelativeProjPoints.relationPoint Px') ⟶
      s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
    (hyR : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) yR ℓR) (n : ℤ) :
    RelativeProjPoints.PullbackTransitionCompatible (XA' := X') (dA := s.relativeProjPoints)
      (dA' := (s.pullback g).relativeProjPoints) (hA := s.relativeProjBaseChangeHom g) Px Px'
      s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor
      hℓt hℓs yU hyU yR hyR (s.twistTransition Px n) ((s.pullback g).twistTransition Px' n)
      (s.baseChangeTwistPieceComparison g ℓ hℓ yU hyU n) :=
  ⟨s.schemePairTransition_baseChangeTwistPieceComparison_of_eq g (U := Px.U) (R := Px.R)
    (U'' := Px'.U) (R'' := Px'.R) (u := Px.toSpace)
    (r := RelativeProjPoints.relationPoint Px) (u'' := Px'.toSpace)
    (r'' := RelativeProjPoints.relationPoint Px') Px.target Px.source rfl
    (s.map_source_comp_toSpace Px)
    (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
    Px'.target Px'.source rfl ((s.pullback g).map_source_comp_toSpace Px')
    (RelativeProjPoints.spaceTarget (B := s.site) (S := s.base) (hS := s.containsBase) (X := X')
      (s.pullback g).relativeProjPoints Px' (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
    (RelativeProjPoints.spaceSource (B := s.site) (S := s.base) (hS := s.containsBase) (X := X')
      (s.pullback g).relativeProjPoints Px' (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
    ((s.pullback g).relativeProjPoints.liesOver_spaceTarget Px'
      (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
    ((s.pullback g).relativeProjPoints.liesOver_spaceSource Px'
      (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
    ℓ hℓ yU hyU ℓR (s.map_relation_comp_relationPoint g Px Px' ℓ hℓ ℓR hℓt) yR hyR
    (RelativeProjPoints.spacePresentation_target_comp_of_liesOverAlong Px Px'
      s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor hℓt
      yU hyU yR hyR)
    (RelativeProjPoints.comp_spacePresentation_source_of_liesOverAlong Px Px'
      s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor hℓs
      yU hyU yR hyR)
    hℓt.symm hℓs n (s.twistTransition Px n) rfl ((s.pullback g).twistTransition Px' n) rfl⟩

/-- The compatibility of the comparison of twists with the transitions, along the morphism of the
presenting schemes `U' ×_{X'} P' ⟶ U ×_X P` induced by `ℓ` and `h`. -/
theorem pullbackTransitionCompatible_chartBaseChangeMap
    (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ) (n : ℤ) :
    RelativeProjPoints.PullbackTransitionCompatible (XA' := X') (dA := s.relativeProjPoints)
      (dA' := (s.pullback g).relativeProjPoints) (hA := s.relativeProjBaseChangeHom g) Px Px'
      s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor
      hℓt hℓs (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
      (s.liesOverAlong_relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
      (s.twistTransition Px n) ((s.pullback g).twistTransition Px' n)
      (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) n) :=
  s.pullbackTransitionCompatible_twistTransition g Px Px' ℓ hℓ ℓR hℓt hℓs _
    (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) _
    (s.liesOverAlong_relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt) n

include hℓt in
/-- **`θ_n : h^*𝒪_P(n) ≅ 𝒪_{P'}(n)`** (Stacks 085C, degreewise): for presentations `X = U/R` and
`X' = U'/R'` compatible with `g` along `ℓ : U' ⟶ U` and `ℓR : R' ⟶ R`, the inverse image along
`h : P' = Proj_{X'}(g^*𝒜) ⟶ P = Proj_X(𝒜)` of the twist `𝒪_P(n)` of Stacks 084D is the twist
`𝒪_{P'}(n)`: the comparison of the twists of Tag 01O3 on the presenting schemes
`U' ×_{X'} P' ⟶ U ×_X P` is compatible with the transitions, so it descends (Stacks 03M3). -/
def baseChangeTwistModuleIso (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ) (n : ℤ) :
    s.pullbackTwistModule g Px n ≅ (s.pullback g).twistModule Px' n :=
  RelativeProjPoints.pullbackAlongDescendedIso (XA' := X') (dA := s.relativeProjPoints)
    (dA' := (s.pullback g).relativeProjPoints) (hA := s.relativeProjBaseChangeHom g) Px Px'
    s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor
    hℓt hℓs (s.chartBaseChangeMap g Px Px' ℓ hℓ) (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ)
    (s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (s.liesOverAlong_relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (s.twistModule Px n) (s.isQuasicoherentOnSite_twistModule Px n) (s.twistTransition Px n)
    (s.twistModuleChartIso Px n) (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
    ((s.pullback g).twistTransition Px' n)
    (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) n)
    (s.pullbackTransitionCompatible_chartBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt hℓs n)
    ((s.pullback g).presentationSchemeCocycle_twistTransition Px' n)
    ((s.pullback g).presentationSchemeUnit_twistTransition Px' n)

/-- **The chart of `θ_n`**: the inverse image of `θ_n` along the atlas `U' ×_{X'} P' ⟶ P'`,
followed by the chart identification of `𝒪_{P'}(n)`, is the identification of `c'^*(h^*𝒪_P(n))`
with `𝒪(n)` on `U' ×_{X'} P'` through the comparison of twists of Tag 01O3. -/
theorem baseChangeTwistModuleIso_spec (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ) (n : ℤ) :
    (modulePullback s.site s.base s.containsBase (presentationAtlas
        (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := X') (s.pullback g).relativeProjPoints Px'
          (s.pullback g).isAlgebraicSpace_relativeProjFunctor))).map
        (s.baseChangeTwistModuleIso g Px Px' ℓ hℓ ℓR hℓt hℓs n).hom.hom ≫
      (presentationDescendedModuleChartIso
        (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := X') (s.pullback g).relativeProjPoints Px'
          (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
        ((s.pullback g).twistPieceQcoh Px'.U Px'.toSpace n) ((s.pullback g).twistTransition Px' n)
        ((s.pullback g).presentationSchemeCocycle_twistTransition Px' n)
        ((s.pullback g).presentationSchemeUnit_twistTransition Px' n)).hom =
    (presentationPullbackChartIso
      (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := X') (s.pullback g).relativeProjPoints Px'
        (s.pullback g).isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (ObjectProperty.homMk (s.relativeProjBaseChangeHom g)) (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (RelativeProjPoints.presentationAtlas_comp_homMk_of_liesOverAlong (XA' := X')
        (dA := s.relativeProjPoints) (dA' := (s.pullback g).relativeProjPoints)
        (hA := s.relativeProjBaseChangeHom g) Px Px' s.isAlgebraicSpace_relativeProjFunctor
        (s.pullback g).isAlgebraicSpace_relativeProjFunctor (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ))
      (s.twistModule Px n) (s.twistModuleChartIso Px n)
      (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
        (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) n)).hom :=
  RelativeProjPoints.pullbackAlongDescendedIso_spec_of_eq (XA' := X') (dA := s.relativeProjPoints)
    (dA' := (s.pullback g).relativeProjPoints) (hA := s.relativeProjBaseChangeHom g) Px Px'
    s.isAlgebraicSpace_relativeProjFunctor (s.pullback g).isAlgebraicSpace_relativeProjFunctor
    hℓt hℓs (s.chartBaseChangeMap g Px Px' ℓ hℓ) (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ)
    (s.relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (s.liesOverAlong_relationBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt)
    (s.twistModule Px n) (s.isQuasicoherentOnSite_twistModule Px n) (s.twistTransition Px n)
    (s.twistModuleChartIso Px n) (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
    ((s.pullback g).twistTransition Px' n)
    (s.baseChangeTwistPieceComparison g ℓ hℓ (s.chartBaseChangeMap g Px Px' ℓ hℓ)
      (s.liesOverAlong_chartBaseChangeMap g Px Px' ℓ hℓ) n)
    (s.pullbackTransitionCompatible_chartBaseChangeMap g Px Px' ℓ hℓ ℓR hℓt hℓs n)
    ((s.pullback g).presentationSchemeCocycle_twistTransition Px' n)
    ((s.pullback g).presentationSchemeUnit_twistTransition Px' n)
    (s.baseChangeTwistModuleIso g Px Px' ℓ hℓ ℓR hℓt hℓs n) rfl

end Theta

end RelativeProjSituation

end AlgebraicGeometry.Space

end
