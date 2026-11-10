module

public import StacksFrontier.AlgebraicGeometry.Quot.MatrixKernelFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.LinearEquationsRepresentableScheme
public import StacksFrontier.AlgebraicGeometry.Quot.AffineLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# The kernel functor of a matrix of functions is represented

Let `c` be a scheme of the big fppf site and `N` an `r × m` matrix of functions on `c`.  The
kernel functor of the morphism `𝒪^r ⟶ 𝒪^m` of `N` on the test schemes over `c`
(`AlgebraicGeometry.Space.matKerFunctor`) is the functor of points of the scheme of solutions of
the linear equations of `N` (`AlgebraicGeometry.linEqScheme`), which is affine and of finite
presentation over `c`.  This is the last step of the proof of Stacks 08JX.

## Main results

* `AlgebraicGeometry.Space.spacePointsOverSchemeEquiv`: the points of the algebraic space of a
  scheme `W` of the site over `c`, at a test scheme `T` over `c`, are the morphisms of schemes
  `T ⟶ W` over `c`.
* `AlgebraicGeometry.Space.exists_matKerFunctor_iso`: the kernel functor of a matrix is
  represented by a scheme of the site affine and of finite presentation over `c`.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The section of the algebraic space of a scheme that a test scheme over it is, is the
morphism of the site underlying the test scheme. -/
theorem testPoint_eq_testMap {c : BigFppfOver B S hS}
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) : testPoint T = testMap T :=
  (congrArg yonedaEquiv (testMap_spec T)).trans (yonedaEquiv_yoneda_map (testMap T))

section Points

variable {c W : BigFppfOver B S hS} (w : W ⟶ c)

/-- A morphism of schemes over the underlying scheme of `c` between underlying schemes of
objects over `c` commutes with their structure morphisms to `S`. -/
theorem comp_inclusion_map_hom_of_comp_eq {T : BigFppfOver B S hS} (t : T ⟶ c)
    (y : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hy : y ≫ (BigFppfOver.toScheme B S hS).map w = (BigFppfOver.toScheme B S hS).map t) :
    y ≫ B.inclusion.map W.hom = B.inclusion.map T.hom := by
  have key : ∀ {X : BigFppfOver B S hS} (g : X ⟶ c),
      B.inclusion.map X.hom = (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map c.hom :=
    fun g => by
      rw [← Over.w g, Functor.map_comp]
      rfl
  rw [key w, ← Category.assoc, hy, key t]

/-- **The points of the algebraic space of a scheme over `c` are morphisms of schemes over `c`.**
At a test scheme `T` over the algebraic space of `c`, the points of the algebraic space of `W`
lying over `T` are the morphisms of schemes from the underlying scheme of `T` to that of `W`
whose composite with `w` is the structure morphism of `T`. -/
def spacePointsOverSchemeEquiv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    spacePointsOverObj ((schemeSpaceFunctor B S hS).map w) T ≃
      {y : (BigFppfOver.toScheme B S hS).obj T.left ⟶ (BigFppfOver.toScheme B S hS).obj W //
        y ≫ (BigFppfOver.toScheme B S hS).map w =
          (BigFppfOver.toScheme B S hS).map (testMap T)} where
  toFun x := ⟨(BigFppfOver.toScheme B S hS).map (x.1 : T.left ⟶ W), by
    have h : (x.1 : T.left ⟶ W) ≫ w = testMap T := x.2.trans (testPoint_eq_testMap T)
    exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map h)⟩
  invFun y := ⟨BigFppfOver.homOfCompEq B S hS y.1
      (comp_inclusion_map_hom_of_comp_eq w (testMap T) y.1 y.2), by
    refine Eq.trans ?_ (testPoint_eq_testMap T).symm
    change BigFppfOver.homOfCompEq B S hS y.1 _ ≫ w = testMap T
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact y.2⟩
  left_inv x := Subtype.ext ((BigFppfOver.toScheme B S hS).map_injective (by
    rw [BigFppfOver.toScheme_map_homOfCompEq]))
  right_inv y := Subtype.ext (BigFppfOver.toScheme_map_homOfCompEq B S hS y.1
    (comp_inclusion_map_hom_of_comp_eq w (testMap T) y.1 y.2))

/-- The morphism of schemes underlying the image of a point under `spacePointsOverSchemeEquiv` is
the image of the underlying morphism under `BigFppfOver.toScheme`. -/
@[simp]
theorem spacePointsOverSchemeEquiv_apply_coe (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (x : spacePointsOverObj ((schemeSpaceFunctor B S hS).map w) T) :
    (spacePointsOverSchemeEquiv w T x).1 = (BigFppfOver.toScheme B S hS).map (x.1 : T.left ⟶ W) :=
  rfl

end Points

section Representable

variable {X Y : Scheme.{u}} (e : X ≅ Y) {C : Scheme.{u}} (p : X ⟶ C) (q : Y ⟶ C)
  (h : p = e.hom ≫ q)

include h in
/-- Morphisms over `C` into isomorphic schemes over `C`. -/
def subtypeHomEquivOfIso {T : Scheme.{u}} (t : T ⟶ C) :
    {y : T ⟶ X // y ≫ p = t} ≃ {y : T ⟶ Y // y ≫ q = t} where
  toFun y := ⟨y.1 ≫ e.hom, by rw [Category.assoc, ← h, y.2]⟩
  invFun y := ⟨y.1 ≫ e.inv, by rw [Category.assoc, h, e.inv_hom_id_assoc, y.2]⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

end Representable

section Kernel

variable (c : BigFppfOver B S hS) {r m : ℕ} (N : Matrix (Fin r) (Fin m) (Gam c))

/-- The values of the kernel functor of a matrix are the solutions of the pulled back
equations, through the coordinates. -/
def kerCoordEquiv (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    (matKerFunctor c N).obj (op T) ≃
      {v : Fin r → Gam T.left // Matrix.vecMul v (pulledMat (N := N) T) = 0} :=
  Equiv.ofBijective (fun α => ⟨kerCoord T α, kerCoord_mem T α⟩)
    ⟨fun _ _ hαβ => kerCoord_injective T (congrArg Subtype.val hαβ),
      fun v => (kerCoord_surjective T v.1 v.2).imp fun _ hα => Subtype.ext hα⟩

/-- The solution associated by `kerCoordEquiv` to a value of the kernel functor is its vector of
coordinates `kerCoord`. -/
@[simp]
theorem kerCoordEquiv_apply_coe (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (α : (matKerFunctor c N).obj (op T)) : (kerCoordEquiv c N T α).1 = kerCoord T α :=
  rfl

/-- The coordinates of a solution depend only on the underlying morphism. -/
theorem linEqHomEquiv_coe_congr {C : Scheme.{u}} {n m' : ℕ} (M : Matrix (Fin n) (Fin m') Γ(C, ⊤))
    {T : Scheme.{u}} {t t' : T ⟶ C} (z : {x : T ⟶ linEqScheme M // x ≫ linEqProj M = t})
    (z' : {x : T ⟶ linEqScheme M // x ≫ linEqProj M = t'}) (h : z.1 = z'.1) :
    (linEqHomEquiv M t z).1 = (linEqHomEquiv M t' z').1 := by
  funext j
  change (z.1 ≫ pullback.fst _ _).appTop _ = (z'.1 ≫ pullback.fst _ _).appTop _
  rw [h]

variable {c N} in
/-- The values of the functor of points of a scheme over `c` isomorphic to the scheme of solutions
of the linear equations of `N` are the values of the kernel functor of `N`. -/
def matKerPointsEquiv {W : BigFppfOver B S hS} (w : W ⟶ c)
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ linEqScheme N)
    (hw : (BigFppfOver.toScheme B S hS).map w = e.hom ≫ linEqProj N)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    (spacePointsOver ((schemeSpaceFunctor B S hS).map w)).obj (op T) ≃
      (matKerFunctor c N).obj (op T) :=
  (spacePointsOverSchemeEquiv w T).trans ((subtypeHomEquivOfIso e _ _ hw _).trans
    ((linEqHomEquiv N _).trans (kerCoordEquiv c N T).symm))

variable {c N} in
/-- The coordinates of the image of a point under `matKerPointsEquiv` are the coordinates of the
corresponding solution of the linear equations of `N`. -/
theorem kerCoord_matKerPointsEquiv {W : BigFppfOver B S hS} (w : W ⟶ c)
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ linEqScheme N)
    (hw : (BigFppfOver.toScheme B S hS).map w = e.hom ≫ linEqProj N)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (x : (spacePointsOver ((schemeSpaceFunctor B S hS).map w)).obj (op T)) :
    kerCoord T (matKerPointsEquiv w e hw T x) =
      (linEqHomEquiv N _ (subtypeHomEquivOfIso e _ _ hw _ (spacePointsOverSchemeEquiv w T x))).1 :=
  congrArg Subtype.val ((kerCoordEquiv c N T).apply_symm_apply _)

variable {c N} in
/-- **The identification of the points with the kernel functor is natural.** -/
theorem matKerPointsEquiv_naturality {W : BigFppfOver B S hS} (w : W ⟶ c)
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ linEqScheme N)
    (hw : (BigFppfOver.toScheme B S hS).map w = e.hom ≫ linEqProj N)
    {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj c)} (f : op T ⟶ op T')
    (x : (spacePointsOver ((schemeSpaceFunctor B S hS).map w)).obj (op T)) :
    matKerPointsEquiv w e hw T' ((spacePointsOver ((schemeSpaceFunctor B S hS).map w)).map f x) =
      (matKerFunctor c N).map f (matKerPointsEquiv w e hw T x) := by
  apply kerCoord_injective T'
  rw [kerCoord_map, kerCoord_matKerPointsEquiv, kerCoord_matKerPointsEquiv]
  let z := subtypeHomEquivOfIso e _ _ hw _ (spacePointsOverSchemeEquiv w T x)
  refine (linEqHomEquiv_coe_congr N _
    ⟨(BigFppfOver.toScheme B S hS).map f.unop.left ≫ z.1, by rw [Category.assoc, z.2]⟩ ?_).trans
    (linEqHomEquiv_comp N _ ((BigFppfOver.toScheme B S hS).map f.unop.left) z)
  exact (congrArg (· ≫ e.hom) ((BigFppfOver.toScheme B S hS).map_comp f.unop.left
    (x.1 : T.left ⟶ W))).trans (Category.assoc _ _ _)

attribute [local irreducible] matKerPointsEquiv in
variable {c N} in
/-- **The functor of points of a scheme over `c` isomorphic to the scheme of solutions of the
linear equations of `N` is the kernel functor of `N`.** -/
def matKerPointsIso {W : BigFppfOver B S hS} (w : W ⟶ c)
    (e : (BigFppfOver.toScheme B S hS).obj W ≅ linEqScheme N)
    (hw : (BigFppfOver.toScheme B S hS).map w = e.hom ≫ linEqProj N) :
    spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙ uliftFunctor.{u + 1, u} ≅
      matKerFunctor c N :=
  NatIso.ofComponents (fun ⟨T⟩ => Equiv.toIso (Equiv.ulift.trans (matKerPointsEquiv w e hw T)))
    (by
      rintro ⟨T⟩ ⟨T'⟩ f
      refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      dsimp only [Functor.comp_map, uliftFunctor_map]
      change (Equiv.ulift.trans (matKerPointsEquiv w e hw T'))
          ((ConcreteCategory.hom (uliftFunctor.{u + 1, u}.map
            ((spacePointsOver ((schemeSpaceFunctor B S hS).map w)).map f))) x) =
        (ConcreteCategory.hom ((matKerFunctor c N).map f))
          ((Equiv.ulift.trans (matKerPointsEquiv w e hw T)) x)
      exact matKerPointsEquiv_naturality w e hw f x.down)

/-- **The kernel functor of a matrix of functions is represented** by a scheme of the site which
is affine and of finite presentation over `c`: the scheme of solutions of the linear equations of
the matrix. -/
theorem exists_matKerFunctor_iso :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ c),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w) ∧
          Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w) ⋙ uliftFunctor.{u + 1, u} ≅
            matKerFunctor c N) := by
  obtain ⟨W, w, e, hw⟩ := exists_siteObject_toScheme_map_eq B S hS
    (contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := c) (linEqProj N)) (linEqProj N)
  refine ⟨W, w, ?_, ?_, ⟨matKerPointsIso w e hw⟩⟩ <;>
  · rw [hw]
    infer_instance

end Kernel

end AlgebraicGeometry.Space

end
