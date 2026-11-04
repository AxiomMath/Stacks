module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeTwoSpace

/-!
# The fibres of `𝐏(ℰ)` as projective bundles, read through the points of `𝐏(ℰ)`

Let `ℰ` be a quasi-coherent module on an algebraic space `X` and `u : T ⟶ X` a scheme point.  The
fibre `𝐏(ℰ)_T` of Stacks 084B is identified with the projective bundle `𝐏((u^*ℰ)_Zar)` of
Tag 01OB (`AlgebraicGeometry.Space.pointFibreProjectiveBundleIso`).  This file relates that
identification to the points of `𝐏(ℰ)`: for a morphism `k : Z ⟶ 𝐏(ℰ)_T` with
`j = k ≫ (𝐏(ℰ)_T ⟶ T)`, the section of `𝐏(((u ∘ j)^*ℰ)_Zar) ⟶ Z` attached to the point `k ≫ t`
of `𝐏(ℰ)`, followed by the base-change morphism of projective bundles of Tag 01O3 along `j`, is
`k` followed by the identification of the fibre.  It also records the class of the image of a
point under `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, the cocycle law of the inverse base-change isomorphisms of the
Zariski reading, and the coherence of the comparisons of inverse images of Stacks 03LU along a
commutative square.

## Main definitions

* `AlgebraicGeometry.Space.pointRelativeProjSection`: the section of `𝐏((x^*ℰ)_Zar) ⟶ T` attached
  to a point of `𝐏(ℰ)` over a scheme point `x`.
* `AlgebraicGeometry.Space.pointTwoSpaceCompIso`: `((u ∘ h ∘ f')^*ℰ) ≅ (v ∘ f')^* g^*ℰ` for
  `v ≫ g = u ∘ h`.

## Main results

* `AlgebraicGeometry.Space.projectiveBundleSectionsEquiv_pointBundleSection`: the class of a point
  is the class of its section under Tag 0B3V.
* `AlgebraicGeometry.Space.pointBundleSection_comp_projectiveBundleBaseChange`: the section of a
  point of the fibre followed by the base change of projective bundles is the identification of
  the fibre.
* `AlgebraicGeometry.Space.pointsEquivInvertibleQuotientClass_projectiveBundleBaseChange`: the
  class of the image of a point under `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackIso_inv_comp`: the cocycle law of the inverse
  base-change isomorphisms of the Zariski reading.
* `AlgebraicGeometry.Space.modulePullbackCompIso_square_coherence`: the comparisons of inverse
  images along the two factorizations of a commutative square.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)

/-- **The section of `𝐏((x^*ℰ)_Zar) ⟶ T` attached to a point of `𝐏(ℰ)` over a scheme point `x`**
(Stacks 084B and the comparison of `x^*Sym(ℰ)` with `Sym(x^*ℰ)`). -/
def pointRelativeProjSection (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (w : {w : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = x}) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    {s : (BigFppfOver.toScheme B S hS).obj T ⟶
        Stacks.RelativeProj.projectiveBundle _ (pointZariskiModule X E T x) //
      s ≫ Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T x) = 𝟙 _} :=
  haveI := isQuasicoherent_pointZariskiModule X E hE T x
  situationSectionsEquiv (pointZariskiModule X E T x) (pointsEquivSections X E hE hb T x w)

/-- The section of the relative Proj attached to a point, through the fibre of Stacks 084B. -/
theorem pointsEquivSections_coe (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (w : {w : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = x}) :
    (pointsEquivSections X E hE hb T x w).1 =
      (BigFppfOver.toScheme B S hS).map
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver T x (𝟙 T)
            ⟨w.1, w.2.trans (yoneda_map_id_comp_eq x).symm⟩).1 ≫
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreIso T x).hom ≫
          (pointProjIso X E hE hb T x).hom :=
  Category.assoc _ _ _

/-- The section attached to a point is the section of the fibre of Stacks 084B followed by the
identification of the fibre with the projective bundle. -/
theorem pointBundleSection_eq (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1)
    (w : {w : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = x}) :
    (pointRelativeProjSection X E hE hb T x w).1 =
      (BigFppfOver.toScheme B S hS).map
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver T x (𝟙 T)
            ⟨w.1, w.2.trans (yoneda_map_id_comp_eq x).symm⟩).1 ≫
        (pointFibreProjectiveBundleIso X E hE hb T x).hom := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  refine (situationSectionsEquiv_apply_coe (pointZariskiModule X E T x) _).trans ?_
  rw [pointsEquivSections_coe]
  simp only [pointFibreProjectiveBundleIso, Iso.trans_hom, Category.assoc]

/-- **The class of a point is the class of its section** under Stacks 0B3V on `T`, through the
dictionary of invertible quotients of Zariski readings. -/
theorem projectiveBundleSectionsEquiv_pointBundleSection (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1)
    (w : {w : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = x}) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    Stacks.RelativeProj.projectiveBundleSectionsEquiv (pointRelativeProjSection X E hE hb T x w) =
      invertibleQuotientClassZariskiEquiv T _ (isQuasicoherentOnSite_pointPullback X E hE T x)
        (pointsEquivInvertibleQuotientClass X E hE hb T x w) := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  refine
    (symmetricSectionsEquivInvertibleQuotientClass_eq (pointZariskiModule X E T x) _).symm.trans ?_
  simp only [pointsEquivInvertibleQuotientClass, Equiv.trans_apply, Equiv.apply_symm_apply]

variable {T : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1)

/-- The section of the fibre attached to the point `k ≫ t` of a morphism `k` into the fibre
`𝐏(ℰ)_T`, followed by the comparison of fibres along `j = k ≫ (𝐏(ℰ)_T ⟶ T)`, is `k`. -/
theorem pointEquivOver_comp_fibreComparison {Z : BigFppfOver B S hS}
    (k : Z ⟶ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T u) (j : Z ⟶ T)
    (hj : k ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T u = j)
    (w : {w : yoneda.obj Z ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = yoneda.map (𝟙 Z) ≫ yoneda.map j ≫ u})
    (hk : yoneda.map k ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u =
      w.1) :
    ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver Z (yoneda.map j ≫ u)
        (𝟙 Z) w).1 ≫
      (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreComparison T u j = k := by
  apply Yoneda.fullyFaithful.map_injective
  refine ((projectiveBundleSituation X E hE hb).relativeProjPoints.isPullback T u).hom_ext ?_ ?_
  · exact ((congrArg (· ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u)
      (yoneda.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (yoneda.map
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver
            Z (yoneda.map j ≫ u) (𝟙 Z) w).1 ≫ ·)
          (RelativeProjPoints.map_fibreComparison_comp_fibreToSpace _ T u j)).trans
          ((RelativeProjPoints.map_pointEquivOver _ Z (yoneda.map j ≫ u) (𝟙 Z) w).trans hk.symm))))
  · exact ((yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ((Category.assoc _ _ _).trans
      ((congrArg (((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver
          Z (yoneda.map j ≫ u) (𝟙 Z) w).1 ≫ ·)
        (RelativeProjPoints.fibreComparison_comp_fibreHom _ T u j)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ j)
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver Z
            (yoneda.map j ≫ u) (𝟙 Z) w).2).trans ((Category.id_comp j).trans hj.symm))))))).trans
      (yoneda.map_comp _ _)

/-- **The section of a point of the fibre, followed by the base change of projective bundles, is
the identification of the fibre**: for `k : Z ⟶ 𝐏(ℰ)_T` with `j = k ≫ (𝐏(ℰ)_T ⟶ T)` and the
point `w = k ≫ t` of `𝐏(ℰ)` over `u ∘ j`, the section `s_w` of `𝐏(((u ∘ j)^*ℰ)_Zar) ⟶ Z` followed
by `𝐏(((u ∘ j)^*ℰ)_Zar) ⟶ 𝐏((u^*ℰ)_Zar)` is `k` followed by the identification of the fibre. -/
theorem pointBundleSection_comp_projectiveBundleBaseChange {Z : BigFppfOver B S hS}
    (k : Z ⟶ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T u) (j : Z ⟶ T)
    (hj : k ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T u = j)
    (w : {w : yoneda.obj Z ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = yoneda.map j ≫ u})
    (hk : yoneda.map k ≫ (projectiveBundleSituation X E hE hb).relativeProjPoints.fibreToSpace T u =
      w.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T u
    haveI := isQuasicoherent_pointZariskiModule X E hE Z (yoneda.map j ≫ u)
    (pointRelativeProjSection X E hE hb Z (yoneda.map j ≫ u) w).1 ≫
        Stacks.RelativeProj.projectiveBundleBaseChange ((BigFppfOver.toScheme B S hS).map j)
          (pointZariskiModule X E T u) (pointZariskiModule X E Z (yoneda.map j ≫ u))
          (pointZariskiModuleBaseChangeIso X E hE u j) =
      (BigFppfOver.toScheme B S hS).map k ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom := by
  have := isQuasicoherent_pointZariskiModule X E hE T u
  have := isQuasicoherent_pointZariskiModule X E hE Z (yoneda.map j ≫ u)
  exact (congrArg (· ≫ Stacks.RelativeProj.projectiveBundleBaseChange
      ((BigFppfOver.toScheme B S hS).map j) (pointZariskiModule X E T u)
      (pointZariskiModule X E Z (yoneda.map j ≫ u)) (pointZariskiModuleBaseChangeIso X E hE u j))
    (pointBundleSection_eq X E hE hb Z (yoneda.map j ≫ u) w)).trans
    ((Category.assoc _ _ _).trans ((congrArg ((BigFppfOver.toScheme B S hS).map
      ((projectiveBundleSituation X E hE hb).relativeProjPoints.pointEquivOver Z
        (yoneda.map j ≫ u) (𝟙 Z) ⟨w.1, w.2.trans (yoneda_map_id_comp_eq _).symm⟩).1 ≫ ·)
      (toScheme_map_fibreComparison_comp_pointFibreProjectiveBundleIso X E hE hb u j)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (pointFibreProjectiveBundleIso X E hE hb T u).hom)
        (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
          (congrArg (BigFppfOver.toScheme B S hS).map
            (pointEquivOver_comp_fibreComparison X E hE hb u k j hj _ hk)))))))

/-- The identification of the fibre with the projective bundle lies over the test object. -/
theorem pointFibreProjectiveBundleIso_hom_comp_projectiveBundleToBase (T : BigFppfOver B S hS)
    (x : yoneda.obj T ⟶ X.1) :
    haveI := isQuasicoherent_pointZariskiModule X E hE T x
    (pointFibreProjectiveBundleIso X E hE hb T x).hom ≫
        Stacks.RelativeProj.projectiveBundleToBase _ (pointZariskiModule X E T x) =
      (BigFppfOver.toScheme B S hS).map
        ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom T x) := by
  have := isQuasicoherent_pointZariskiModule X E hE T x
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·)
      (situationProjectiveBundleIso_hom_toBase (pointZariskiModule X E T x)).symm).trans
      (pointProjIso_hom_toBase X E hE hb T x))))).trans
    ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibreHom_comp T x).symm

/-- If `f ≫ j.hom = i.hom ≫ f'` for isomorphisms `i` and `j`, then `i.inv ≫ f = f' ≫ j.inv`. -/
theorem _root_.CategoryTheory.inv_comp_eq_comp_inv_of_comp_hom_eq {𝒞 : Type*} [Category 𝒞]
    {A A' B B' : 𝒞} (i : A ≅ A') (j : B ≅ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (H : f ≫ j.hom = i.hom ≫ f') : i.inv ≫ f = f' ≫ j.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, H]

/-- If `pc.inv ≫ a.hom ≫ b.hom ≫ m = z.hom` for isomorphisms `pc`, `a`, `b` and `z`, then
`b.inv ≫ a.inv ≫ pc.hom = m ≫ z.inv`. -/
theorem _root_.CategoryTheory.inv_comp_inv_comp_hom_eq_of_cocycle {𝒞 : Type*} [Category 𝒞]
    {X₀ X₁ X₂ X₃ X₄ : 𝒞} (pc : X₁ ≅ X₀) (a : X₁ ≅ X₂) (b : X₂ ≅ X₃) (m : X₃ ⟶ X₄) (z : X₀ ≅ X₄)
    (c : pc.inv ≫ a.hom ≫ b.hom ≫ m = z.hom) : b.inv ≫ a.inv ≫ pc.hom = m ≫ z.inv := by
  rw [Iso.eq_comp_inv, ← c]
  simp

section ZariskiCocycle

variable {T₀ T₁ T₂ : BigFppfOver B S hS}

/-- **The inverse base-change isomorphisms of the Zariski reading are natural.** -/
theorem zariskiReadingPullbackIso_inv_naturality (τ : T₁ ⟶ T₀)
    {M N : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (α : M ⟶ N) :
    (zariskiReadingPullbackIso τ M hM).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).map
          ((zariskiReadingFunctor T₀).map α) =
      (zariskiReadingFunctor T₁).map
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).map α) ≫
        (zariskiReadingPullbackIso τ N hN).inv :=
  CategoryTheory.inv_comp_eq_comp_inv_of_comp_hom_eq _ _ _ _
    ((zariskiReadingPullbackHom τ).naturality α)

/-- **The cocycle law of the inverse base-change isomorphisms of the Zariski reading**, along a
composite `τ₁ ≫ τ₂` of test objects. -/
theorem zariskiReadingPullbackIso_inv_comp (τ₁ : T₂ ⟶ T₁) (τ₂ : T₁ ⟶ T₀)
    (N : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀))
    (hN : N.IsQuasicoherentOnSite)
    (hN' : ((modulePullback B S hS (representedSpaceMap B S hS τ₂)).obj N).IsQuasicoherentOnSite) :
    (zariskiReadingPullbackIso τ₁ _ hN').inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).map
          (zariskiReadingPullbackIso τ₂ N hN).inv ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂)).hom.app ((zariskiReadingFunctor T₀).obj N) =
      (zariskiReadingFunctor T₂).map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS τ₁) (representedSpaceMap B S hS τ₂)).hom.app N) ≫
        (zariskiReadingPullbackIso (τ₁ ≫ τ₂) N hN).inv :=
  CategoryTheory.inv_comp_inv_comp_hom_eq_of_cocycle
    ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ₁)
      ((BigFppfOver.toScheme B S hS).map τ₂)).app ((zariskiReadingFunctor T₀).obj N))
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).mapIso
      (zariskiReadingPullbackIso τ₂ N hN))
    (zariskiReadingPullbackIso τ₁ _ hN') _ (zariskiReadingPullbackIso (τ₁ ≫ τ₂) N hN)
    (zariskiReadingPullbackHom_comp τ₁ τ₂ N)

end ZariskiCocycle

section PointClass

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))

/-- **The class of the image of a point under `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`** is the class of the point,
transported along `(x' ≫ g)^*ℰ ≅ x'^* g^*ℰ`, with the point of `X` given up to equality. -/
theorem pointsEquivInvertibleQuotientClass_projectiveBundleBaseChange {Z : BigFppfOver B S hS}
    (x' : yoneda.obj Z ⟶ X'.1)
    (w' : {w : yoneda.obj Z ⟶ (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').1 //
      w ≫ (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').hom = x'})
    (x₂ : yoneda.obj Z ⟶ X.1) (hx : x' ≫ g.hom = x₂)
    (w₂ : {w : yoneda.obj Z ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      w ≫ (projectiveBundleπ X E hE hb).hom = x₂})
    (hw : w'.1 ≫ (projectiveBundleBaseChange X E hE hb g hb').hom = w₂.1) :
    pointsEquivInvertibleQuotientClass X E hE hb Z x₂ w₂ =
      invertibleQuotientTransportClass
        (eqToIso (congrArg (fun y => (modulePullback B S hS (pointHom y)).obj E) hx.symm) ≪≫
          pointCompIso g E Z x')
        (pointsEquivInvertibleQuotientClass X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' Z x' w') := by
  subst hx
  have e : w₂ = baseChangePointOfPointsEquiv g E (projectiveBundleπ X E hE hb)
      (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
      (pointsEquivInvertibleQuotientClass X E hE hb)
      (pointsEquivInvertibleQuotientClass X' _ _ hb') Z x' w' := by
    obtain ⟨w', rfl⟩ := w'
    refine Subtype.ext (hw.symm.trans ?_)
    exact (comp_baseChangeHomOfPointsEquiv_hom g E _ _ _ _ _ _ Z w').trans
      (baseChangePointOfPointsEquiv_congr g E _ _ _ _ Z rfl _ _ rfl)
  subst e
  exact (Equiv.apply_symm_apply _ _).trans (by rw [eqToIso_refl, Iso.refl_trans])

end PointClass

/-- If `x.inv ≫ y.inv = z.inv ≫ w` for isomorphisms `x`, `y` and `z`, then
`w ≫ y.hom = z.hom ≫ x.inv`. -/
theorem _root_.CategoryTheory.comp_hom_eq_hom_comp_inv_of_inv_comp_eq {𝒞 : Type*} [Category 𝒞]
    {O₁ O₂ O₃ O₄ : 𝒞} (x : O₂ ≅ O₁) (y : O₃ ≅ O₂) (z : O₄ ≅ O₁) (w : O₄ ⟶ O₃)
    (H : x.inv ≫ y.inv = z.inv ≫ w) : w ≫ y.hom = z.hom ≫ x.inv := by
  have hw : w = z.hom ≫ x.inv ≫ y.inv := by rw [H, Iso.hom_inv_id_assoc]
  rw [hw]
  simp

section ModuleCoherence

variable {W Y Y₂ X₁ X₀ : AlgebraicSpaces B S hS}

/-- Inverse images along equal morphisms of algebraic spaces are equal. -/
theorem modulePullback_congr {Y X₀ : AlgebraicSpaces B S hS} {d d' : Y ⟶ X₀} (hd : d = d') :
    modulePullback B S hS d = modulePullback B S hS d' :=
  congrArg (modulePullback B S hS) hd

/-- The comparison `a^* d^* ≅ (d ∘ a)^*` along equal morphisms `d = d'`. -/
theorem modulePullbackCompIso_inv_app_map_eqToHom_hom_app (a : W ⟶ Y) {d d' : Y ⟶ X₀}
    (hd : d = d') (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS a d).inv.app M ≫
        (modulePullback B S hS a).map ((eqToHom (modulePullback_congr hd)).app M) ≫
        (modulePullbackCompIso B S hS a d').hom.app M =
      eqToHom (show (modulePullback B S hS (a ≫ d)).obj M = (modulePullback B S hS (a ≫ d')).obj M
        by rw [hd]) := by
  subst hd
  simp

/-- The associativity coherence of Stacks 03LU, with the inner comparison moved across. -/
theorem modulePullbackCompIso_inv_app_inv_app_map_hom_app (a : W ⟶ Y) (b : Y ⟶ X₁)
    (c : X₁ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) =
      (modulePullbackCompIso B S hS a (b ≫ c)).inv.app M := by
  rw [reassoc_of% (modulePullbackCompIso_assoc_inv_app B S hS a b c M),
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- `modulePullbackCompIso_inv_app_inv_app_map_hom_app` with the associativity of the composite
carried by an explicit identification. -/
theorem modulePullbackCompIso_inv_app_inv_app_map_hom_app_eqToHom (a : W ⟶ Y) (b : Y ⟶ X₁)
    (c : X₁ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) =
      eqToHom (show (modulePullback B S hS ((a ≫ b) ≫ c)).obj M =
          (modulePullback B S hS (a ≫ (b ≫ c))).obj M by rw [Category.assoc]) ≫
        (modulePullbackCompIso B S hS a (b ≫ c)).inv.app M :=
  (modulePullbackCompIso_inv_app_inv_app_map_hom_app a b c M).trans
    (by simp)

/-- `modulePullbackCompIso_assoc_inv_app` rearranged, with the associativity of the composite
carried by an explicit identification. -/
theorem modulePullbackCompIso_map_inv_app_hom_app_eqToHom (a : W ⟶ Y) (b' : Y ⟶ Y₂)
    (c' : Y₂ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b' c').inv.app M) ≫
        (modulePullbackCompIso B S hS a b').hom.app ((modulePullback B S hS c').obj M) =
      (modulePullbackCompIso B S hS a (b' ≫ c')).hom.app M ≫
        eqToHom (show (modulePullback B S hS (a ≫ (b' ≫ c'))).obj M =
          (modulePullback B S hS ((a ≫ b') ≫ c')).obj M by rw [Category.assoc]) ≫
        (modulePullbackCompIso B S hS (a ≫ b') c').inv.app M :=
  (CategoryTheory.comp_hom_eq_hom_comp_inv_of_inv_comp_eq
      ((modulePullbackCompIso B S hS (a ≫ b') c').app M)
      ((modulePullbackCompIso B S hS a b').app ((modulePullback B S hS c').obj M))
      ((modulePullbackCompIso B S hS a (b' ≫ c')).app M) _
      (modulePullbackCompIso_assoc_inv_app B S hS a b' c' M)).trans
    (congrArg (_ ≫ ·) (by simp))

/-- Pasting `x ≫ y ≫ aH = e₁ ≫ p`, `p ≫ aE ≫ q = e₂` and `aI ≫ j = q ≫ e₃ ≫ k` along
`e₀ ≫ e₁ ≫ e₂ ≫ e₃ = 𝟙` gives `e₀ ≫ x ≫ y ≫ aH ≫ aE ≫ aI ≫ j = k`. -/
theorem _root_.CategoryTheory.modulePullbackCompIso_square_paste {𝒞 : Type*} [Category 𝒞]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : 𝒞} (e₀ : O₀ ⟶ O₁) (x : O₁ ⟶ O₂) (y : O₂ ⟶ O₃)
    (aH : O₃ ⟶ O₄) (aE : O₄ ⟶ O₅) (aI : O₅ ⟶ O₆) (j : O₆ ⟶ O₇) (k : O₀ ⟶ O₇)
    (e₁ : O₁ ⟶ O₈) (p : O₈ ⟶ O₄) (q : O₅ ⟶ O₉) (e₃ : O₉ ⟶ O₀) (e₂ : O₈ ⟶ O₉)
    (L1 : x ≫ y ≫ aH = e₁ ≫ p) (L2 : aI ≫ j = q ≫ e₃ ≫ k) (L3 : p ≫ aE ≫ q = e₂)
    (L4 : e₀ ≫ e₁ ≫ e₂ ≫ e₃ = 𝟙 O₀) : e₀ ≫ x ≫ y ≫ aH ≫ aE ≫ aI ≫ j = k := by
  rw [reassoc_of% L1, L2, reassoc_of% L3, reassoc_of% L4]

/-- The inverse images along the two factorizations of a commutative square `b ≫ c = b' ≫ c'`,
preceded by `a`, agree. -/
theorem modulePullback_obj_square_eq (a : W ⟶ Y) (b : Y ⟶ X₁) (c : X₁ ⟶ X₀)
    (b' : Y ⟶ Y₂) (c' : Y₂ ⟶ X₀) (hbc : b ≫ c = b' ≫ c') (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullback B S hS ((a ≫ b') ≫ c')).obj M =
      (modulePullback B S hS ((a ≫ b) ≫ c)).obj M := by
  rw [Category.assoc, Category.assoc, hbc]

/-- **The comparisons of inverse images along the two factorizations of a commutative square
`b ≫ c = b' ≫ c'`, preceded by `a`** (Stacks 03LU). -/
theorem modulePullbackCompIso_square_coherence (a : W ⟶ Y) (b : Y ⟶ X₁) (c : X₁ ⟶ X₀)
    (b' : Y ⟶ Y₂) (c' : Y₂ ⟶ X₀) (hbc : b ≫ c = b' ≫ c') (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    eqToHom (modulePullback_obj_square_eq a b c b' c' hbc M) ≫
        (modulePullbackCompIso B S hS (a ≫ b) c).inv.app M ≫
        (modulePullbackCompIso B S hS a b).inv.app ((modulePullback B S hS c).obj M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b c).hom.app M) ≫
        (modulePullback B S hS a).map ((eqToHom (modulePullback_congr hbc)).app M) ≫
        (modulePullback B S hS a).map ((modulePullbackCompIso B S hS b' c').inv.app M) ≫
        (modulePullbackCompIso B S hS a b').hom.app ((modulePullback B S hS c').obj M) =
      (modulePullbackCompIso B S hS (a ≫ b') c').inv.app M :=
  CategoryTheory.modulePullbackCompIso_square_paste _ _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullbackCompIso_inv_app_inv_app_map_hom_app_eqToHom a b c M)
    (modulePullbackCompIso_map_inv_app_hom_app_eqToHom a b' c' M)
    (modulePullbackCompIso_inv_app_map_eqToHom_hom_app a hbc M)
    ((eqToHom_trans_assoc _ _ _).trans ((eqToHom_trans_assoc _ _ _).trans
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))))

/-- The comparison `a^* c^* ≅ (a ≫ c)^*` along equal morphisms `a = a'`. -/
theorem modulePullbackCompIso_inv_app_of_eq {x y : W ⟶ X₁} (e : x = y) (c : X₁ ⟶ X₀)
    (M : Modules.{u, u} B S hS X₀.1 X₀.2) :
    (modulePullbackCompIso B S hS x c).inv.app M =
      eqToHom (show (modulePullback B S hS (x ≫ c)).obj M = (modulePullback B S hS (y ≫ c)).obj M
          by rw [e]) ≫ (modulePullbackCompIso B S hS y c).inv.app M ≫
        eqToHom (show (modulePullback B S hS y).obj ((modulePullback B S hS c).obj M) =
          (modulePullback B S hS x).obj ((modulePullback B S hS c).obj M) by rw [e]) := by
  subst e
  simp

end ModuleCoherence



/-- The composite of the images of four composable morphisms under a functor is the image of
their composite. -/
theorem _root_.CategoryTheory.Functor.map_comp_four {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) {A₀ A₁ A₂ A₃ A₄ : 𝒞} (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃)
    (f₄ : A₃ ⟶ A₄) : F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ = F.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄) := by
  simp only [Functor.map_comp]

/-- Pasting `rφ ≫ r₁ ≫ rα ≫ rm = r₀`, `z₁ ≫ pα = rα ≫ z₁'` and `z₁' ≫ pz₂ ≫ pc = rm ≫ z₀`, with
`pe = pα ≫ pz₂` and `pq = 𝟙`, gives `r₀ ≫ z₀ = (rφ ≫ r₁ ≫ z₁) ≫ pe ≫ pc ≫ pq`. -/
theorem _root_.CategoryTheory.pointZariskiModule_twoSpace_paste {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₉ : 𝒞} (r₀ : A₀ ⟶ A₁) (z₀ : A₁ ⟶ A₂) (rφ : A₀ ⟶ A₃)
    (r₁ : A₃ ⟶ A₄) (z₁ : A₄ ⟶ A₅) (pe : A₅ ⟶ A₆) (pc : A₆ ⟶ A₂) (pq : A₂ ⟶ A₂)
    (rα : A₄ ⟶ A₇) (rm : A₇ ⟶ A₁) (z₁' : A₇ ⟶ A₉) (pα : A₅ ⟶ A₉) (pz₂ : A₉ ⟶ A₆)
    (hR : rφ ≫ r₁ ≫ rα ≫ rm = r₀) (C2 : z₁ ≫ pα = rα ≫ z₁')
    (C1 : z₁' ≫ pz₂ ≫ pc = rm ≫ z₀) (hp : pe = pα ≫ pz₂) (hq : pq = 𝟙 A₂) :
    r₀ ≫ z₀ = (rφ ≫ r₁ ≫ z₁) ≫ pe ≫ pc ≫ pq := by
  rw [hq, hp, ← hR]
  simp only [Category.assoc, Category.comp_id]
  rw [reassoc_of% C2, C1]

section TwoSpaceCocycle

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {T' : BigFppfOver B S hS}
  (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T) (hvh : v ≫ g.hom = yoneda.map h ≫ u)

include hvh in
/-- The point `u ∘ h ∘ f'` of `X` is `g ∘ v ∘ f'`. -/
theorem yoneda_map_comp_point_twoSpace {Z : BigFppfOver B S hS} (f' : Z ⟶ T') :
    (yoneda.map f' ≫ v) ≫ g.hom = yoneda.map (f' ≫ h) ≫ u := by
  rw [Category.assoc, hvh, ← Category.assoc, ← Functor.map_comp]

/-- The identification `((u ∘ h ∘ f')^*ℰ) ≅ (v ∘ f')^* g^*ℰ` of the inverse images of `ℰ` along the
two factorizations of the point `u ∘ h ∘ f' = g ∘ v ∘ f'` (Stacks 03LU). -/
def pointTwoSpaceCompIso {Z : BigFppfOver B S hS} (f' : Z ⟶ T') :
    (modulePullback B S hS (pointHom (yoneda.map (f' ≫ h) ≫ u))).obj E ≅
      (modulePullback B S hS (pointHom (yoneda.map f' ≫ v))).obj
        ((modulePullback B S hS g).obj E) :=
  eqToIso (show (modulePullback B S hS (pointHom (yoneda.map (f' ≫ h) ≫ u))).obj E =
      (modulePullback B S hS (pointHom ((yoneda.map f' ≫ v) ≫ g.hom))).obj E by
        rw [yoneda_map_comp_point_twoSpace X u g v h hvh f']) ≪≫
    pointCompIso g E Z (yoneda.map f' ≫ v)

/-- A square `eS ≫ x₀ ≫ y ≫ aH ≫ aE ≫ aI ≫ j = k₀`, with its edges identified up to identities and
an inverse pair `ε₂i ≫ ε₂ = 𝟙`, gives `(eφ ≫ x) ≫ y ≫ A ≫ j = k`. -/
theorem _root_.CategoryTheory.comp_eq_of_square_of_eqToHom {𝒞 : Type*} [Category 𝒞]
    {P₀ P₀' P₁ P₁' P₂ P₂' P₃ P₄ P₅ P₆ P₇ : 𝒞} (eφ : P₀ ⟶ P₁) (eS : P₀' ⟶ P₁') (ε₁ : P₁' ⟶ P₁)
    (x : P₁ ⟶ P₂) (ε₁' : P₂ ⟶ P₂) (y : P₂ ⟶ P₃) (aH : P₃ ⟶ P₄) (aE : P₄ ⟶ P₅) (aI : P₅ ⟶ P₆)
    (j : P₆ ⟶ P₇) (A : P₃ ⟶ P₆) (ε₂ : P₀' ⟶ P₀) (ε₂i : P₀ ⟶ P₀') (k : P₀ ⟶ P₇) (ε₂' : P₇ ⟶ P₇)
    (x₀ : P₁' ⟶ P₂) (k₀ : P₀' ⟶ P₇) (sq : eS ≫ x₀ ≫ y ≫ aH ≫ aE ≫ aI ≫ j = k₀)
    (b₁ : x₀ = ε₁ ≫ x ≫ ε₁') (b₂ : k₀ = ε₂ ≫ k ≫ ε₂')
    (hA : A = aH ≫ aE ≫ aI) (h₁ : ε₁' = 𝟙 P₂) (h₂ : ε₂' = 𝟙 P₇) (h₃ : ε₂i ≫ ε₂ = 𝟙 P₀)
    (h₄ : eφ = ε₂i ≫ eS ≫ ε₁) : (eφ ≫ x) ≫ y ≫ A ≫ j = k := by
  rw [b₁, b₂, h₁, h₂] at sq
  rw [h₄, hA]
  simp only [Category.assoc, Category.comp_id] at sq ⊢
  rw [sq, reassoc_of% h₃]

end TwoSpaceCocycle

end AlgebraicGeometry.Space

end
