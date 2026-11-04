module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationAffineAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtalePointSections

/-!
# The kernel of an adjoint map under étale base change

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces and `v : f^*F ⟶ H` a morphism
of modules with adjoint `F ⟶ f_*H`.  When the base change map `g^*f_*H ⟶ f'_*(g')^*H` is an
isomorphism — for instance for a cartesian square with `g` étale (Stacks 03LX) — the inverse image
along `g` of the adjoint kills exactly the sections killed by the adjoint, along `f'`, of
`(g')^*v` precomposed with the comparison `(f')^*g^*F ≅ (g')^*f^*F`.  For `g` étale the sections of
`g^*F` are the sections of `F` over the étale charts through `g` (Stacks 03LW), so the kernel of
the adjoint over such a chart is computed on the base change.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.modulePullback_map_homEquiv_val_app_eq_zero_iff`: the
  kernel of `g^*` of an adjoint, through the base change map.
* `AlgebraicGeometry.Space.C1359Bridge.homEquiv_val_app_etaleChart_eq_zero_iff`: for a cartesian
  square with `g` étale, the kernel of the adjoint over the chart `g ∘ V`.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) {F : Modules.{u, u} B S hS Y.1 Y.2} {H : Modules.{u, u} B S hS X.1 X.2}

/-- **The kernel of the inverse image of an adjoint, through the base change map.**  If the base
change map `g^*f_*H ⟶ f'_*(g')^*H` is an isomorphism, `g^*` of the adjoint of `v : f^*F ⟶ H` kills
a section exactly when the adjoint along `f'` of `(g')^*v`, precomposed with the comparison of the
two composite inverse images, does. -/
theorem modulePullback_map_homEquiv_val_app_eq_zero_iff (comm : g' ≫ f = f' ≫ g)
    [IsIso ((moduleBaseChangeMap f g f' g' comm).app H)]
    (v : (modulePullback B S hS f).obj F ⟶ H) (W : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (x : ((modulePullback B S hS g).obj F).val.obj W) :
    ((modulePullback B S hS g).map
        ((modulePullbackAdjunction B S hS f).homEquiv F H v)).val.app W x = 0 ↔
      ((modulePullbackAdjunction B S hS f').homEquiv _ _
        ((modulePullbackSquareComparison f g f' g' comm).inv.app F ≫
          (modulePullback B S hS g').map v)).val.app W x = 0 := by
  rw [← homEquiv_comp_moduleBaseChangeMap f g f' g' comm v]
  exact RelativeProjSituation.eq_zero_iff_iso_hom_val_app_eq_zero
    (asIso ((moduleBaseChangeMap f g f' g' comm).app H)) W _

/-- **The kernel of an adjoint over an étale chart, computed on the base change.**  For a cartesian
square `g' ≫ f = f' ≫ g` with `g` étale, the adjoint of `v : f^*F ⟶ H` kills the section of `F`
over the chart `g ∘ V` read off a section `x` of `g^*F` over `V` (Stacks 03LW) exactly when the
adjoint along `f'` of `(g')^*v`, precomposed with the comparison of the two composite inverse
images, kills `x`. -/
theorem homEquiv_val_app_etaleChart_eq_zero_iff (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (v : (modulePullback B S hS f).obj F ⟶ H)
    (V : SmallEtale B S hS Y'.1) (x : ((modulePullback B S hS g).obj F).val.obj (op V)) :
    ((modulePullbackAdjunction B S hS f).homEquiv F H v).val.app
        (op ((smallEtalePostcomp B S hS g hg).obj V))
        (((modulePullbackIsoEtaleModulePullback B S hS g hg).app F).hom.val.app (op V) x) = 0 ↔
      ((modulePullbackAdjunction B S hS f').homEquiv _ _
        ((modulePullbackSquareComparison f g f' g' sq.w).inv.app F ≫
          (modulePullback B S hS g').map v)).val.app (op V) x = 0 := by
  have : IsIso (moduleBaseChangeMap f g f' g' sq.w) :=
    isIso_moduleBaseChangeMap_of_isEtale B S hS g' f' f g sq hg
  rw [← RelativeProjSituation.modulePullbackIsoEtaleModulePullback_hom_naturality_apply g hg
    ((modulePullbackAdjunction B S hS f).homEquiv F H v) V x]
  exact (RelativeProjSituation.eq_zero_iff_iso_hom_val_app_eq_zero
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).app _) (op V) _).symm.trans
    (modulePullback_map_homEquiv_val_app_eq_zero_iff f g f' g' sq.w v (op V) x)

/-- A morphism followed by an isomorphism kills a section exactly when the morphism does. -/
theorem comp_iso_hom_val_app_eq_zero_iff {Z : AlgebraicSpaces B S hS}
    {M H H' : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ H) (e : H ≅ H')
    (W : (SmallEtale B S hS Z.1)ᵒᵖ) (x : M.val.obj W) :
    (φ ≫ e.hom).val.app W x = 0 ↔ φ.val.app W x = 0 :=
  (RelativeProjSituation.eq_zero_iff_iso_hom_val_app_eq_zero e W (φ.val.app W x)).symm

/-- A morphism followed by an invertible morphism kills a section exactly when the morphism
does. -/
theorem comp_isIso_val_app_eq_zero_iff {Z : AlgebraicSpaces B S hS}
    {M H H' : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ H) (e : H ⟶ H') [IsIso e]
    (W : (SmallEtale B S hS Z.1)ᵒᵖ) (x : M.val.obj W) :
    (φ ≫ e).val.app W x = 0 ↔ φ.val.app W x = 0 :=
  comp_iso_hom_val_app_eq_zero_iff φ (asIso e) W x

/-- **The kernel of `𝒜 ⟶ π_*i_*i^*𝒦` over an étale chart, computed on the base changes.**  For
cartesian squares `c ≫ π = f' ≫ g` and `c_Z ≫ i = j ≫ c` with `g` and `c` étale, the adjoint of
`ψ ≫ η_i : π^*F ⟶ 𝒦 ⟶ i_*i^*𝒦` kills the section of `F` over the chart `g ∘ V` read off a section
`x` of `g^*F` (Stacks 03LW) exactly when the adjoint along `f'` of `c^*ψ ≫ η_j`, precomposed with
the comparison of the two composite inverse images, kills `x`. -/
theorem homEquiv_comp_unit_val_app_etaleChart_eq_zero_iff {X P Z U P' Z' : AlgebraicSpaces B S hS}
    (π : P ⟶ X) (i : Z ⟶ P) (g : U ⟶ X) (c : P' ⟶ P) (f' : P' ⟶ U) (cZ : Z' ⟶ Z) (j : Z' ⟶ P')
    (sq : IsPullback c f' π g) (sqZ : IsPullback cZ j i c) (hg : IsEtale B S hS g.hom)
    (hc : IsEtale B S hS c.hom) {F : Modules.{u, u} B S hS X.1 X.2}
    {K : Modules.{u, u} B S hS P.1 P.2} (ψ : (modulePullback B S hS π).obj F ⟶ K)
    (V : SmallEtale B S hS U.1) (x : ((modulePullback B S hS g).obj F).val.obj (op V)) :
    ((modulePullbackAdjunction B S hS π).homEquiv F _
        (ψ ≫ (modulePullbackAdjunction B S hS i).unit.app K)).val.app
        (op ((smallEtalePostcomp B S hS g hg).obj V))
        (((modulePullbackIsoEtaleModulePullback B S hS g hg).app F).hom.val.app (op V) x) = 0 ↔
      ((modulePullbackAdjunction B S hS f').homEquiv ((modulePullback B S hS g).obj F)
        ((modulePushforward B S hS j).obj ((modulePullback B S hS j).obj
          ((modulePullback B S hS c).obj K)))
        ((modulePullbackSquareComparison π g f' c sq.w).inv.app F ≫
          (modulePullback B S hS c).map ψ ≫
            (modulePullbackAdjunction B S hS j).unit.app
              ((modulePullback B S hS c).obj K))).val.app (op V) x = 0 := by
  have : IsIso (moduleBaseChangeMap i c j cZ sqZ.w) :=
    isIso_moduleBaseChangeMap_of_isEtale B S hS cZ j i c sqZ hc
  have key : (modulePullback B S hS c).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
      (moduleBaseChangeMap i c j cZ sqZ.w).app ((modulePullback B S hS i).obj K) =
      (modulePullbackAdjunction B S hS j).unit.app _ ≫ (modulePushforward B S hS j).map
        ((modulePullbackSquareComparison i c j cZ sqZ.w).inv.app K) := by
    have h := homEquiv_comp_moduleBaseChangeMap i c j cZ sqZ.w
      (𝟙 ((modulePullback B S hS i).obj K))
    rw [Adjunction.homEquiv_id, (modulePullbackAdjunction B S hS j).homEquiv_unit] at h
    simpa using h
  refine (homEquiv_val_app_etaleChart_eq_zero_iff π g f' c sq hg _ V x).trans ?_
  refine (comp_iso_hom_val_app_eq_zero_iff _ ((modulePushforward B S hS f').mapIso
    (asIso ((moduleBaseChangeMap i c j cZ sqZ.w).app
      ((modulePullback B S hS i).obj K)))) (op V) x).symm.trans ?_
  rw [Functor.mapIso_hom, asIso_hom, ← Adjunction.homEquiv_naturality_right, Functor.map_comp,
    Category.assoc, Category.assoc, key, ← Category.assoc, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, Category.assoc]
  exact comp_isIso_val_app_eq_zero_iff _ _ (op V) x

end AlgebraicGeometry.Space.C1359Bridge

end
