module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomBaseChangeCone
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Quot.ZarConeRelHomSheaf

/-!
# The relative Hom functor of Stacks 08JT as a relative Hom functor of a pullback datum

The relative Hom functor `T ↦ Hom(F_T, G_T)` of Stacks 08JT is the relative Hom functor of the
inverse image of modules of Stacks 03LU, as a pullback pseudofunctor datum, over the cone of the
base changes `X_T ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.homFunctorIsoRelHom`: the identification.

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

-- The comparisons below are definitional; unfolding the inverse image of modules or the base
-- change functor while checking them only makes the unifier explore the small étale topoi.
attribute [local irreducible] modulePullback baseChangeOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restriction in a relative Hom functor is conjugation by the comparison of the datum. -/
theorem _root_.CategoryTheory.PullbackData.relHomFunctor_map_eq_ofHom {A : Type*} [Category* A]
    {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D) (hP : P.IsCoherent)
    {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A} (κ : PullbackData.ConeTo π a₀) (M N : D a₀)
    {i j : Iᵒᵖ} (g : i ⟶ j) :
    (P.relHomFunctor hP κ M N).map g =
      TypeCat.ofHom (Functor.conjHom (P.triangle (κ.w g.unop))) :=
  rfl

/-- The base changes `X_T` of `f`, spelled as the relative Hom functor of Stacks 08JT reads
them. -/
abbrev homTestBaseChanges {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SchemesOver Y ⥤ AlgebraicSpaces B S hS where
  obj T := ((baseChangeOver f).op.obj (op T)).unop.left
  map g := ((baseChangeOver f).op.map g.op).unop.left
  map_id T := by simp
  map_comp g h := by simp

/-- The projections `X_T ⟶ X`, spelled as the relative Hom functor of Stacks 08JT reads them, as
a cone of test objects over `X`. -/
abbrev homTestBaseChangeCone {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    PullbackData.ConeTo (homTestBaseChanges f) X where
  leg T := ((baseChangeOver f).op.obj (op T)).unop.hom
  w g := Over.w ((baseChangeOver f).op.map g.op).unop

/-- Restriction along `T ⟶ T'` in the relative Hom functor of Stacks 08JT is conjugation by the
comparison of the inverse image of modules along the base change `X_T' ⟶ X_T`. -/
theorem HomSituation.homFunctor_map_eq_ofHom (s : HomSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) {T T' : (s.SchemesOver)ᵒᵖ} (g : T ⟶ T') :
    (s.homFunctor hc).map g = TypeCat.ofHom (Functor.conjHom
      (modulePullbackTriangle B S hS (Over.w ((baseChangeOver s.f).op.map g).unop))) :=
  rfl

/-- Restriction in the relative Hom functor of Stacks 08JT agrees with restriction in the relative
Hom functor of `modulePullbackData` over `homTestBaseChangeCone`. -/
theorem HomSituation.homFunctor_map_eq_relHomFunctor_map (s : HomSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) {T T' : (s.SchemesOver)ᵒᵖ} (g : T ⟶ T') :
    (s.homFunctor hc).map g = ((modulePullbackData B S hS).relHomFunctor
      (modulePullbackData_isCoherent B S hS) (homTestBaseChangeCone s.f) s.F s.G).map g := by
  rw [s.homFunctor_map_eq_ofHom hc g, PullbackData.relHomFunctor_map_eq_ofHom,
    modulePullbackData_triangle]
  rfl

/-- **The relative Hom functor of Stacks 08JT is the relative Hom functor of the inverse image
of modules of Stacks 03LU over the base changes `X_T ⟶ X`.** -/
def HomSituation.homFunctorIsoRelHom (s : HomSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) :
    s.homFunctor hc ≅ (modulePullbackData B S hS).relHomFunctor
      (modulePullbackData_isCoherent B S hS) (homTestBaseChangeCone s.f) s.F s.G :=
  NatIso.ofComponents (fun T => Iso.refl _) (fun {T T'} g => by
    rw [s.homFunctor_map_eq_relHomFunctor_map hc g]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The comparison of the inverse image of modules, in the spelling of the small étale topoi,
along a presented composite is the comparison of Stacks 03LU. -/
theorem toposModulePullbackData_triangle {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    (toposModulePullbackData B S hS).triangle hk = modulePullbackTriangle B S hS hk :=
  rfl

/-- Restriction in the relative Hom functor of `toposModulePullbackData` over
`homTestBaseChangeCone f` agrees with restriction in that of `modulePullbackData`. -/
theorem toposModulePullbackData_relHomFunctor_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F G : Modules.{u, u} B S hS X.1 X.2) {T T' : (SchemesOver Y)ᵒᵖ} (g : T ⟶ T') :
    ((toposModulePullbackData B S hS).relHomFunctor (toposModulePullbackData_isCoherent B S hS)
        (homTestBaseChangeCone f) F G).map g =
      ((modulePullbackData B S hS).relHomFunctor (modulePullbackData_isCoherent B S hS)
        (homTestBaseChangeCone f) F G).map g := by
  rw [PullbackData.relHomFunctor_map_eq_ofHom (modulePullbackData B S hS),
    modulePullbackData_triangle]
  refine (PullbackData.relHomFunctor_map_eq_ofHom (toposModulePullbackData B S hS)
    (toposModulePullbackData_isCoherent B S hS) (homTestBaseChangeCone f)
    (show toposModules B S hS X from F) (show toposModules B S hS X from G) g).trans ?_
  rw [toposModulePullbackData_triangle]
  rfl

/-- The relative Hom functor of the inverse image of modules over the base changes does not
depend on the spelling of the categories of modules. -/
def toposModulePullbackDataRelHomIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (F G : Modules.{u, u} B S hS X.1 X.2) :
    (toposModulePullbackData B S hS).relHomFunctor (toposModulePullbackData_isCoherent B S hS)
        (homTestBaseChangeCone f) F G ≅
      (modulePullbackData B S hS).relHomFunctor (modulePullbackData_isCoherent B S hS)
        (homTestBaseChangeCone f) F G :=
  NatIso.ofComponents (fun T => Iso.refl _) (fun {T T'} g => by
    rw [toposModulePullbackData_relHomFunctor_map f F G g]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicGeometry.Space
