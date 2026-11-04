module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.ProjMap

/-!
# Morphisms of base changes along the morphism of functors of quadruples

The comparison morphisms of Stacks 084B (3) lie over the morphisms of test objects; the comparison
`v^*𝒜' ≅ k^*(u^*𝒜)` of the restricted algebras along `k` and `g`
(`GradedAlgebraRestriction.ComapHom.compRestrict`); and, on schemes, a morphism lying over `k` and
`h` is the identification of the restricted algebras followed by the base-change morphism of
Tag 01O3.
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

/-! ### The morphisms of base changes along the morphism of functors of quadruples -/

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : X' ⟶ X}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    {Â' : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X') →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ₁ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    {ρ₁' : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â')}
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hc' : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'),
      B.Contains (relativeProj (Â' T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')

/-- The comparison morphism of Stacks 084B (3) lies over `k` for the functor of quadruples. -/
theorem liesOver_projComparison {Z Z' : BigFppfOver B S hS} (f : yoneda.obj Z ⟶ X)
    (k : Z' ⟶ Z) :
    (ρ₁.quadrupleRelativeProjPoints hc hX).LiesOver (ρ₁.projComparison hc f k) k :=
  ⟨(ρ₁.isPullback_projComparison hc f k).1.w, ρ₁.projToQuadrupleSpace_comp hc hX f k⟩

/-- The comparison morphism of Stacks 084B (3), read at an equal point, is the identification of
the restrictions followed by the base-change morphism of Tag 01O3. -/
theorem toScheme_map_eqToHom_projComparison {Z Z' : BigFppfOver B S hS} (f : yoneda.obj Z ⟶ X)
    (k : Z' ⟶ Z) (f' : yoneda.obj Z' ⟶ X) (hf : yoneda.map k ≫ f = f') :
    (BigFppfOver.toScheme B S hS).map
        (eqToHom (congrArg ((ρ₁.quadrupleRelativeProjPoints hc hX).fibre Z') hf.symm) ≫
          ρ₁.projComparison hc f k) =
      (relativeProjCongr (A₁ := Â Z' f')
        (A₂ := (Â Z f).pullback ((BigFppfOver.toScheme B S hS).map k))
        (ρ₁.restrict k f f' hf) (ρ₁.isIso_restrict_app k f f' hf)).hom ≫
        baseChangeHom (Â Z f) ((BigFppfOver.toScheme B S hS).map k) := by
  subst hf
  exact (congrArg (BigFppfOver.toScheme B S hS).map (Category.id_comp _)).trans
    (ρ₁.toScheme_map_projComparison hc f k)

/-- The comparison morphism of Stacks 084B (3), read at an equal point, lies over `k`. -/
theorem liesOver_eqToHom_comp_projComparison {Z Z' : BigFppfOver B S hS} (f : yoneda.obj Z ⟶ X)
    (k : Z' ⟶ Z) {f' : yoneda.obj Z' ⟶ X} (hf : f' = yoneda.map k ≫ f) :
    (ρ₁.quadrupleRelativeProjPoints hc hX).LiesOver
      (eqToHom (congrArg ((ρ₁.quadrupleRelativeProjPoints hc hX).fibre Z') hf) ≫
        ρ₁.projComparison hc f k) k := by
  subst hf
  exact ⟨(Category.id_comp _).trans (ρ₁.isPullback_projComparison hc f k).1.w,
    (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
      ((Category.id_comp _).trans (ρ₁.projToQuadrupleSpace_comp hc hX f k))⟩

namespace ComapHom

variable {ρ₁} (e₁ : ComapHom ρ₁' ρ₁ g)

/-- **The comparison of the restricted algebras along `k` and `g`**: for scheme points `u` of `X`
and `v` of `X'` with `u ∘ k = g ∘ v`, the composite `v^*𝒜' ≅ (g v)^*𝒜 ≅ k^*(u^*𝒜)` of the
comparison along `g` and the restriction along `k`. -/
def compRestrict {U V : BigFppfOver B S hS} (k : V ⟶ U) (u : yoneda.obj U ⟶ X)
    (v : yoneda.obj V ⟶ X') (hv : yoneda.map k ≫ u = v ≫ g) :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra (Â' V v))
      (situationAlgebra ((Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))) :=
  (e₁.hom v).comp (ρ₁.restrict k u (v ≫ g) hv)

/-- The comparison of the restricted algebras is invertible in every degree. -/
instance isIso_compRestrict_app {U V : BigFppfOver B S hS} (k : V ⟶ U) (u : yoneda.obj U ⟶ X)
    (v : yoneda.obj V ⟶ X') (hv : yoneda.map k ≫ u = v ≫ g) (n : ℤ) :
    IsIso ((e₁.compRestrict k u v hv).app n) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (e₁.isIso_hom_app v n) (ρ₁.isIso_restrict_app k u (v ≫ g) hv n)

/-- The fibre map lies over the identity and over the morphism of the functors of quadruples. -/
theorem liesOverAlong_projMap {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    (ρ₁'.quadrupleRelativeProjPoints hc' hX').LiesOverAlong (ρ₁.quadrupleRelativeProjPoints hc hX)
      (e₁.quadrupleSpaceMap hc hc' hX hX') (e₁.projMap hc hc' f') (𝟙 T) :=
  ⟨(e₁.projMap_comp_projHom hc hc' f').trans (Category.comp_id _).symm,
    e₁.map_projMap_comp_projToQuadrupleSpace hc hc' hX hX' f'⟩

/-- The fibre map followed by a morphism of base changes of `P` lying over `k` lies over
`𝟙 ≫ k`. -/
theorem liesOverAlong_projMap_comp {U V : BigFppfOver B S hS}
    {u : yoneda.obj U ⟶ X} {v : yoneda.obj V ⟶ X'} {k : V ⟶ U}
    (x : (ρ₁.quadrupleRelativeProjPoints hc hX).fibre V (v ≫ g) ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u)
    (hx : (ρ₁.quadrupleRelativeProjPoints hc hX).LiesOver x k) :
    (ρ₁'.quadrupleRelativeProjPoints hc' hX').LiesOverAlong (ρ₁.quadrupleRelativeProjPoints hc hX)
      (e₁.quadrupleSpaceMap hc hc' hX hX') (e₁.projMap hc hc' v ≫ x) (𝟙 V ≫ k) :=
  (e₁.liesOverAlong_projMap hc hc' hX hX' v).comp_liesOver hx

/-- A morphism of base changes lying over `k` and over the morphism of the functors of quadruples
factors as the fibre map followed by any morphism of base changes of `P` lying over `k`. -/
theorem eq_projMap_comp_of_liesOverAlong {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    {v : yoneda.obj V ⟶ X'} {k : V ⟶ U}
    (x : (ρ₁.quadrupleRelativeProjPoints hc hX).fibre V (v ≫ g) ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u)
    (hx : (ρ₁.quadrupleRelativeProjPoints hc hX).LiesOver x k)
    {y : (ρ₁'.quadrupleRelativeProjPoints hc' hX').fibre V v ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u}
    (hy : (ρ₁'.quadrupleRelativeProjPoints hc' hX').LiesOverAlong
      (ρ₁.quadrupleRelativeProjPoints hc hX) (e₁.quadrupleSpaceMap hc hc' hX hX') y k) :
    y = e₁.projMap hc hc' v ≫ x :=
  hy.eq (e₁.liesOverAlong_projMap_comp hc hc' hX hX' x hx) (Category.id_comp k).symm

/-- The identification of relative Projs along
`AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.compRestrict` is the composite of the
identifications along its two factors. -/
theorem relativeProjCongr_compRestrict {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    {v : yoneda.obj V ⟶ X'} {k : V ⟶ U} (hv : yoneda.map k ≫ u = v ≫ g) :
    (relativeProjCongr (A₁ := Â' V v)
        (A₂ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))
        (e₁.compRestrict k u v hv) (e₁.isIso_compRestrict_app k u v hv)).hom =
      (relativeProjCongr (A₁ := Â' V v) (A₂ := Â V (v ≫ g)) (e₁.hom v)
          (e₁.isIso_hom_app v)).hom ≫
        (relativeProjCongr (A₁ := Â V (v ≫ g))
          (A₂ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))
          (ρ₁.restrict k u (v ≫ g) hv) (ρ₁.isIso_restrict_app k u (v ≫ g) hv)).hom :=
  relativeProjCongr_comp_hom (A₁ := Â' V v) (A₂ := Â V (v ≫ g))
    (A₃ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k)) (e₁.hom v)
    (e₁.isIso_hom_app v) (ρ₁.restrict k u (v ≫ g) hv)
    (ρ₁.isIso_restrict_app k u (v ≫ g) hv) (e₁.isIso_compRestrict_app k u v hv)

/-- On schemes, the fibre map followed by a morphism of base changes of `P` which is, on schemes,
the identification along the restriction followed by the base-change morphism of Tag 01O3, is the
identification along `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.compRestrict`
followed by the base-change morphism. -/
theorem toScheme_map_projMap_comp {U V : BigFppfOver B S hS}
    {u : yoneda.obj U ⟶ X} {v : yoneda.obj V ⟶ X'} {k : V ⟶ U}
    (hv : yoneda.map k ≫ u = v ≫ g)
    (x : (ρ₁.quadrupleRelativeProjPoints hc hX).fibre V (v ≫ g) ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u)
    (hx : (BigFppfOver.toScheme B S hS).map x =
      (relativeProjCongr (A₁ := Â V (v ≫ g))
        (A₂ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))
        (ρ₁.restrict k u (v ≫ g) hv) (ρ₁.isIso_restrict_app k u (v ≫ g) hv)).hom ≫
        baseChangeHom (Â U u) ((BigFppfOver.toScheme B S hS).map k)) :
    (BigFppfOver.toScheme B S hS).map (e₁.projMap hc hc' v ≫ x) =
      (relativeProjCongr (A₁ := Â' V v)
        (A₂ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))
        (e₁.compRestrict k u v hv) (e₁.isIso_compRestrict_app k u v hv)).hom ≫
        baseChangeHom (Â U u) ((BigFppfOver.toScheme B S hS).map k) :=
  ((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    ((congrArg₂ (· ≫ ·) (e₁.toScheme_map_projMap hc hc' v) hx).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ baseChangeHom (Â U u)
        ((BigFppfOver.toScheme B S hS).map k)) (e₁.relativeProjCongr_compRestrict hv).symm)))

/-- **A morphism of base changes lying over `k` and over the morphism of the functors of
quadruples is, on schemes, the identification of the restricted algebras along
`AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.compRestrict` followed by the
base-change morphism of Tag 01O3.** -/
theorem toScheme_map_eq_of_liesOverAlong {U V : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    {v : yoneda.obj V ⟶ X'} {k : V ⟶ U} (hv : yoneda.map k ≫ u = v ≫ g)
    {y : (ρ₁'.quadrupleRelativeProjPoints hc' hX').fibre V v ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u}
    (hy : (ρ₁'.quadrupleRelativeProjPoints hc' hX').LiesOverAlong
      (ρ₁.quadrupleRelativeProjPoints hc hX) (e₁.quadrupleSpaceMap hc hc' hX hX') y k) :
    (BigFppfOver.toScheme B S hS).map y =
      (relativeProjCongr (A₁ := Â' V v)
        (A₂ := (Â U u).pullback ((BigFppfOver.toScheme B S hS).map k))
        (e₁.compRestrict k u v hv) (e₁.isIso_compRestrict_app k u v hv)).hom ≫
        baseChangeHom (Â U u) ((BigFppfOver.toScheme B S hS).map k) :=
  (congrArg (BigFppfOver.toScheme B S hS).map (e₁.eq_projMap_comp_of_liesOverAlong hc hc' hX hX'
    _ (ρ₁.liesOver_eqToHom_comp_projComparison hc hX u k hv.symm) hy)).trans
    (e₁.toScheme_map_projMap_comp hc hc' hX hv _
      (ρ₁.toScheme_map_eqToHom_projComparison hc hX u k (v ≫ g) hv))

/-- A morphism of base changes lying over `k` and over the morphism of the functors of quadruples
commutes with the structure morphisms of the two relative homogeneous spectra. -/
theorem toScheme_map_comp_toBase_of_liesOverAlong {U V : BigFppfOver B S hS}
    {u : yoneda.obj U ⟶ X} {v : yoneda.obj V ⟶ X'} {k : V ⟶ U}
    {y : (ρ₁'.quadrupleRelativeProjPoints hc' hX').fibre V v ⟶
      (ρ₁.quadrupleRelativeProjPoints hc hX).fibre U u}
    (hy : (ρ₁'.quadrupleRelativeProjPoints hc' hX').LiesOverAlong
      (ρ₁.quadrupleRelativeProjPoints hc hX) (e₁.quadrupleSpaceMap hc hc' hX hX') y k) :
    (BigFppfOver.toScheme B S hS).map y ≫ (relativeProj (Â U u)).toBase =
      (relativeProj (Â' V v)).toBase ≫ (BigFppfOver.toScheme B S hS).map k :=
  ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme B S hS).map hy.1).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _))

/-- **The first cocycle condition of the comparisons of the restricted algebras**: along `k ≫ k₀`
the comparison is the comparison along `k` followed by the restriction along `k₀` pulled back. -/
theorem congrHom_compRestrict_comp {U V W : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    {v : yoneda.obj V ⟶ X'} {w : yoneda.obj W ⟶ X} (k : V ⟶ U) (k₀ : U ⟶ W)
    (hv : yoneda.map k ≫ u = v ≫ g) (hu : yoneda.map k₀ ≫ w = u)
    (hv' : yoneda.map (k ≫ k₀) ≫ w = v ≫ g) (n : ℕ) :
    (congrHom (e₁.compRestrict (k ≫ k₀) w v hv')).app (n : ℤ) =
      (congrHom (e₁.compRestrict k u v hv)).app (n : ℤ) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k)).map
          ((congrHom (A₁ := Â U u) (A₂ := (Â W w).pullback ((BigFppfOver.toScheme B S hS).map k₀))
            (ρ₁.restrict k₀ w u hu)).app (n : ℤ)) ≫
          Stacks.AlgebraicGeometry.ModuleLimits.canHom ((BigFppfOver.toScheme B S hS).map k)
            ((BigFppfOver.toScheme B S hS).map k₀) ((BigFppfOver.toScheme B S hS).map (k ≫ k₀))
            ((BigFppfOver.toScheme B S hS).map_comp k k₀).symm ((Â W w).piece (n : ℤ)) :=
  (congrArg ((e₁.hom v).app (n : ℤ) ≫ ·)
    (congrArg (fun Ψ => SheafOfModules.GradedAlgebra.UnitalHom.app Ψ (n : ℤ))
      (ρ₁.restrict_comp k₀ k w u (v ≫ g) hu hv hv'))).trans (Category.assoc _ _ _).symm

/-- The chase behind the second cocycle condition, at variables. -/
private theorem comp_eq_of_restrict_comp {C : Type*} [Category C] {a b c d e f₀ : C}
    (H'' : a ⟶ b) (R'' : b ⟶ f₀) (Rk' : b ⟶ c) (BR : c ⟶ e) (can : e ⟶ f₀) (r' : a ⟶ d)
    (BH : d ⟶ c) (PBHR : d ⟶ e) (h1 : R'' = Rk' ≫ BR ≫ can) (h2 : r' ≫ BH = H'' ≫ Rk')
    (h3 : PBHR = BH ≫ BR) : H'' ≫ R'' = r' ≫ PBHR ≫ can := by
  rw [h1, h3, ← reassoc_of% h2]
  simp only [Category.assoc]

/-- **The second cocycle condition of the comparisons of the restricted algebras**: along
`k' ≫ k` the comparison is the restriction of `𝒜'` along `k'` followed by the comparison along `k`
pulled back. -/
theorem congrHom_restrict_comp_compRestrict {U V V' : BigFppfOver B S hS} {u : yoneda.obj U ⟶ X}
    {v : yoneda.obj V ⟶ X'} {v' : yoneda.obj V' ⟶ X'} (k : V ⟶ U) (k' : V' ⟶ V)
    (hv : yoneda.map k ≫ u = v ≫ g) (hw : yoneda.map k' ≫ v = v')
    (hv' : yoneda.map (k' ≫ k) ≫ u = v' ≫ g) (n : ℕ) :
    (congrHom (e₁.compRestrict (k' ≫ k) u v' hv')).app (n : ℤ) =
      (congrHom (A₁ := Â' V' v') (A₂ := (Â' V v).pullback ((BigFppfOver.toScheme B S hS).map k'))
          (ρ₁'.restrict k' v v' hw)).app (n : ℤ) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k')).map
          ((congrHom (e₁.compRestrict k u v hv)).app (n : ℤ)) ≫
          Stacks.AlgebraicGeometry.ModuleLimits.canHom ((BigFppfOver.toScheme B S hS).map k')
            ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map (k' ≫ k))
            ((BigFppfOver.toScheme B S hS).map_comp k' k).symm ((Â U u).piece (n : ℤ)) := by
  have hk' : yoneda.map k' ≫ v ≫ g = v' ≫ g := by rw [← Category.assoc, hw]
  exact comp_eq_of_restrict_comp _ _ _ _ _ _ _ _
    (congrArg (fun Ψ => SheafOfModules.GradedAlgebra.UnitalHom.app Ψ (n : ℤ))
      (ρ₁.restrict_comp k k' u (v ≫ g) (v' ≫ g) hv hk' hv'))
    (congrArg (fun Ψ => SheafOfModules.GradedAlgebra.UnitalHom.app Ψ (n : ℤ))
      (e₁.restrict_comp_hom k' v v' hw hk'))
    (Functor.map_comp _ _ _)

end ComapHom

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
