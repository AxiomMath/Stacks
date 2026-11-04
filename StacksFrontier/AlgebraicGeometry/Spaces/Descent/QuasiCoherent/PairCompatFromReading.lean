module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairChartConnect
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCanonicalDescent

/-!
# The pairwise condition of a descent datum from the reading of its charts

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  Suppose a descent datum `D` relative to that family has been
identified, member by member, with the canonical descent datum of an `𝒪_X`-module `M`: for each
`i` an isomorphism `τ i : (f i)^*M ≅ D.F i` of the étale restriction with the `i`-th component,
and the isomorphism `θ i : D.F i ≅ (f i)^*M` of Stacks 03LU it induces through the comparison of
Stacks 03LW.

This file proves that the family `θ` intertwines the pairwise isomorphisms of `D` with the
canonical comparisons of Stacks 04W5, granted that the readings `τ` are compatible over the charts
of the pairwise fibre products. That compatibility is the hypothesis `hT` below, a statement
about sections: restricting a section of `M` along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of a chart of `Y i ×_X Y j` and
reading it through `τ j` is reading it through `τ i` and transporting it by the pairwise
isomorphism of `D`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transition_naturality_of_pairReading`: the
  pairwise condition of the identification, the equation of morphisms of modules on
  `Y i ×_X Y j` which makes `θ` a morphism of descent data.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transition_naturality_val_app_of_pairReading`:
  the same equation read on sections over a chart of the pairwise fibre product.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_map_theta_reading`: the
  left-hand side of that equation, read over a chart of the pairwise fibre product, is the
  reading through `τ i` restricted along the connecting morphism of the chart.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### Isomorphisms of modules and readings of sections, inverted -/

/-- An isomorphism of modules, read on sections over a chart: it undoes its inverse. -/
theorem iso_val_app_inv_hom {A : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (e : M ≅ N) (U : SmallEtale B S hS A.1)
    (x : N.val.obj (.op U)) :
    e.hom.val.app (.op U) (e.inv.val.app (.op U) x) = x :=
  CategoryTheory.congr_fun (congrArg (fun t : N ⟶ N => t.val.app (.op U)) e.inv_hom_id) x

/-- An isomorphism of modules, read on sections over a chart: its inverse undoes it. -/
theorem iso_val_app_hom_inv {A : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (e : M ≅ N) (U : SmallEtale B S hS A.1)
    (x : M.val.obj (.op U)) :
    e.inv.val.app (.op U) (e.hom.val.app (.op U) x) = x :=
  CategoryTheory.congr_fun (congrArg (fun t : M ⟶ M => t.val.app (.op U)) e.hom_inv_id) x

/-- Two morphisms of modules which agree on every chart are equal. -/
theorem hom_ext_of_val_app {A : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} {φ ψ : M ⟶ N}
    (h : ∀ U : SmallEtale B S hS A.1, φ.val.app (.op U) = ψ.val.app (.op U)) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Uop => h Uop.unop)

/-- The reading of sections of Stacks 03LW is injective: it has the two-sided inverse
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSectInv`. -/
theorem etaleSect_injective {A C : AlgebraicSpaces B S hS} (g : A ⟶ C)
    (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS A.1)
    {m m' : ((modulePullback B S hS g).obj M).val.obj (.op U)}
    (h : etaleSect B S hS g hg M U m = etaleSect B S hS g hg M U m') : m = m' :=
  ((etaleSectInv_etaleSect B S hS g hg M U m).symm.trans
      (congrArg (etaleSectInv B S hS g hg M U) h)).trans
    (etaleSectInv_etaleSect B S hS g hg M U m')

/-! ### Restriction along a morphism of charts carrying an identity -/

/-- Restriction of sections along a morphism of charts whose underlying morphism of the big fppf
site is an identity is the transport along an equality of those charts. -/
theorem val_map_eq_eqToHom_of_hom_left_id {A : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS A.1 A.2) {U V : SmallEtale B S hS A.1} (E : U = V)
    (k : V ⟶ U) (hk : HEq k.hom.left (𝟙 U.1.left)) (t : N.val.obj (.op U)) :
    N.val.map k.op t =
      eqToHom (congrArg (fun W : SmallEtale B S hS A.1 => N.val.presheaf.obj (.op W)) E) t := by
  subst E
  obtain rfl : k = 𝟙 U := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (eq_of_heq hk))
  simp only [eqToHom_refl, op_id]
  exact CategoryTheory.congr_fun (N.val.map_id (.op U)) t

/-! ### The reading of a prescribed identification of a module with a component -/

/-- The reading of sections cancels the identification it induces: if `θ₀` is the
isomorphism of a module `G` with the inverse image of `M` obtained from an isomorphism `τ₀` of
the étale restriction of `M` with `G` through the comparison of Stacks 03LW, then reading a
section of `G` carried by `θ₀` is applying the inverse of `τ₀` to it. -/
theorem etaleSect_theta_val_app {A C : AlgebraicSpaces B S hS} (g : A ⟶ C)
    (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS C.1 C.2)
    (G : Modules.{u, u} B S hS A.1 A.2)
    (τ₀ : (etaleModulePullback.{u, u} B S hS g hg).obj M ≅ G)
    (θ₀ : G ≅ (modulePullback B S hS g).obj M)
    (hθ₀ : θ₀.hom = τ₀.inv ≫ ((modulePullbackIsoEtaleModulePullback B S hS g hg).app M).inv)
    (U : SmallEtale B S hS A.1) (s : G.val.obj (.op U)) :
    etaleSect B S hS g hg M U (θ₀.hom.val.app (.op U) s) = τ₀.inv.val.app (.op U) s := by
  have h1 : θ₀.hom.val.app (.op U) s =
      ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (.op U)
        (τ₀.inv.val.app (.op U) s) :=
    congrArg (fun q : G ⟶ (modulePullback B S hS g).obj M => q.val.app (.op U) s) hθ₀
  rw [h1]
  exact natIso_hom_inv_val_app B S hS (modulePullbackIsoEtaleModulePullback B S hS g hg) M U
    (τ₀.inv.val.app (.op U) s)

/-- Reading a section of the inverse image of `G` carried by the inverse image of `θ₀`,
over a chart and then over the composite chart, is reading it over the chart and applying the
inverse of `τ₀`. -/
theorem etaleSect_etaleSect_map_theta {A C P : AlgebraicSpaces B S hS} (b : P ⟶ A)
    (hb : IsEtale B S hS b.hom) (g : A ⟶ C) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C.1 C.2) (G : Modules.{u, u} B S hS A.1 A.2)
    (τ₀ : (etaleModulePullback.{u, u} B S hS g hg).obj M ≅ G)
    (θ₀ : G ≅ (modulePullback B S hS g).obj M)
    (hθ₀ : θ₀.hom = τ₀.inv ≫ ((modulePullbackIsoEtaleModulePullback B S hS g hg).app M).inv)
    (Z : SmallEtale B S hS P.1) (x : ((modulePullback B S hS b).obj G).val.obj (.op Z)) :
    etaleSect B S hS g hg M ((smallEtalePostcomp B S hS b hb).obj Z)
        (etaleSect B S hS b hb ((modulePullback B S hS g).obj M) Z
          (((modulePullback B S hS b).map θ₀.hom).val.app (.op Z) x)) =
      τ₀.inv.val.app (.op ((smallEtalePostcomp B S hS b hb).obj Z))
        (etaleSect B S hS b hb G Z x) :=
  (congrArg (etaleSect B S hS g hg M ((smallEtalePostcomp B S hS b hb).obj Z))
      (etaleSect_map B S hS b hb θ₀.hom Z x)).trans
    (etaleSect_theta_val_app B S hS g hg M G τ₀ θ₀ hθ₀
      ((smallEtalePostcomp B S hS b hb).obj Z) (etaleSect B S hS b hb G Z x))

/-! ### The two sides of the pairwise condition over a chart of a fibre product -/

/-- The inverse image along the first projection of the identification, followed by the
canonical comparison of Stacks 04W5 and read over the chart of `X` induced by the second
projection, is the reading through `τ i` restricted along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of the chart. -/
theorem canonicalComparison_map_theta_reading
    (D : DescentDatum B S hS Yi f) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
    (θ : ∀ i, D.F i ≅ (modulePullback B S hS (f i)).obj M)
    (hθ : ∀ i, (θ i).hom = (τ i).inv ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (f i) (hf i)).app M).inv)
    (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (m : ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj (D.F i)).val.obj (.op Z)) :
    etaleSect B S hS (f j) (hf j) M
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (etaleSect B S hS (pairSnd B S hS Yi f i j) (isEtale_pairSnd B S hS Yi f hf i j)
          ((modulePullback B S hS (f j)).obj M) Z
          ((canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
              (pair_condition B S hS Yi f i j) M).hom.val.app (.op Z)
            (((modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom).val.app
              (.op Z) m))) =
      M.val.map (pairChartConnect B S hS Yi f hf Z).op
        ((τ i).inv.val.app
          (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z))
          (etaleSect B S hS (pairFst B S hS Yi f i j) (isEtale_pairFst B S hS Yi f hf i j)
            (D.F i) Z m)) := by
  rw [canonicalComparison_etaleSect B S hS
      (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
      (pair_condition B S hS Yi f i j) (isEtale_pairFst B S hS Yi f hf i j)
      (isEtale_pairSnd B S hS Yi f hf i j) (hf i) (hf j)
      (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
      (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
      (ModulePullbackCompIsoEtaleRestriction.toComp B S hS
        (AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction B S hS)
        (pairFst B S hS Yi f i j) (f i) _ _ _)
      (ModulePullbackCompIsoEtaleRestriction.toComp B S hS
        (AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction B S hS)
        (pairSnd B S hS Yi f i j) (f j) _ _ _)
      M Z,
    etaleSect_etaleSect_map_theta B S hS (pairFst B S hS Yi f i j)
      (isEtale_pairFst B S hS Yi f hf i j) (f i) (hf i) M (D.F i) (τ i) (θ i) (hθ i) Z m]
  exact (val_map_eq_eqToHom_of_hom_left_id B S hS M
    (smallEtalePostcomp_obj_congr B S hS
      (isEtale_comp B S hS (isEtale_pairFst B S hS Yi f hf i j) (hf i))
      (isEtale_comp B S hS (isEtale_pairSnd B S hS Yi f hf i j) (hf j))
      (pair_condition B S hS Yi f i j) Z)
    (pairChartConnect B S hS Yi f hf Z)
    (heq_of_eq (pairChartConnect_hom_left B S hS Yi f hf Z)) _).symm

/-- The pairwise condition of the identification, read on sections over a chart of the pairwise
fibre product. -/
theorem transition_naturality_val_app_of_pairReading
    (D : DescentDatum B S hS Yi f) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
    (θ : ∀ i, D.F i ≅ (modulePullback B S hS (f i)).obj M)
    (hθ : ∀ i, (θ i).hom = (τ i).inv ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (f i) (hf i)).app M).inv)
    (hT : ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (σ : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
      (τ j).hom.val.app
          (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
          (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
        etaleSect B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
          ((D.transition i j).hom.val.app (.op Z)
            (etaleSectInv B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
              ((τ i).hom.val.app
                (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                  (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ))))
    (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
    (m : ((modulePullback B S hS (pairFst B S hS Yi f i j)).obj (D.F i)).val.obj (.op Z)) :
    (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
          (pair_condition B S hS Yi f i j) M).hom.val.app (.op Z)
        (((modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom).val.app (.op Z) m) =
      ((modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom).val.app (.op Z)
        ((D.transition i j).hom.val.app (.op Z) m) := by
  refine etaleSect_injective B S hS (pairSnd B S hS Yi f i j)
    (isEtale_pairSnd B S hS Yi f hf i j) ((modulePullback B S hS (f j)).obj M) Z ?_
  refine etaleSect_injective B S hS (f j) (hf j) M
    ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
      (isEtale_pairSnd B S hS Yi f hf i j)).obj Z) ?_
  rw [canonicalComparison_map_theta_reading B S hS Yi f hf D M τ θ hθ i j Z m,
    etaleSect_etaleSect_map_theta B S hS (pairSnd B S hS Yi f i j)
      (isEtale_pairSnd B S hS Yi f hf i j) (f j) (hf j) M (D.F j) (τ j) (θ j) (hθ j) Z
      ((D.transition i j).hom.val.app (.op Z) m)]
  have hTi := hT i j Z
    ((τ i).inv.val.app
      (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j)).obj Z))
      (etaleSect B S hS (pairFst B S hS Yi f i j) (isEtale_pairFst B S hS Yi f hf i j)
        (D.F i) Z m))
  rw [iso_val_app_inv_hom, etaleSectInv_etaleSect] at hTi
  exact (iso_val_app_hom_inv B S hS (τ j) _ _).symm.trans (congrArg ((τ j).inv.val.app _) hTi)

/-- The pairwise condition of the identification, read as an equality of maps of the sections
over a chart of the pairwise fibre product. -/
theorem transition_naturality_val_of_pairReading
    (D : DescentDatum B S hS Yi f) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
    (θ : ∀ i, D.F i ≅ (modulePullback B S hS (f i)).obj M)
    (hθ : ∀ i, (θ i).hom = (τ i).inv ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (f i) (hf i)).app M).inv)
    (hT : ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (σ : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
      (τ j).hom.val.app
          (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
          (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
        etaleSect B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
          ((D.transition i j).hom.val.app (.op Z)
            (etaleSectInv B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
              ((τ i).hom.val.app
                (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                  (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ))))
    (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    ((modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
          (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
            (pair_condition B S hS Yi f i j) M).hom).val.app (.op Z) =
      ((D.transition i j).hom ≫
          (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom).val.app (.op Z) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  refine (comp_val_app B S hS
      ((modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom)
      (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
        (pair_condition B S hS Yi f i j) M).hom Z m).trans ?_
  refine Eq.trans ?_ (comp_val_app B S hS (D.transition i j).hom
    ((modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom) Z m).symm
  exact transition_naturality_val_app_of_pairReading B S hS Yi f hf D M τ θ hθ hT i j Z m

/-! ### The pairwise condition -/

/-- Given, for each member of the family, an isomorphism `τ i` of the étale restriction of an
`𝒪_X`-module `M` with the `i`-th component of a descent datum `D`, and the isomorphism `θ i` of
Stacks 03LU it induces through the comparison of Stacks 03LW, the family `θ` intertwines the
pairwise isomorphisms of `D` with the canonical comparisons of Stacks 04W5 as soon as the
readings `τ` are compatible over the charts of the pairwise fibre products.

That compatibility, the hypothesis `hT`, is a statement about sections alone: restricting a
section of `M` along the connecting morphism
`AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` of a chart of `Y i ×_X Y j` and
reading it through `τ j` is reading it through `τ i` and transporting it by the pairwise
isomorphism of `D`.  This is the equation that makes `θ` a morphism of descent data. -/
theorem transition_naturality_of_pairReading
    (D : DescentDatum B S hS Yi f) (M : Modules.{u, u} B S hS X.1 X.2)
    (τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i)
    (θ : ∀ i, D.F i ≅ (modulePullback B S hS (f i)).obj M)
    (hθ : ∀ i, (θ i).hom = (τ i).inv ≫
      ((modulePullbackIsoEtaleModulePullback B S hS (f i) (hf i)).app M).inv)
    (hT : ∀ (i j : I) (Z : SmallEtale B S hS (pair B S hS Yi f i j).1)
        (σ : M.val.obj (.op ((smallEtalePostcomp B S hS (f i) (hf i)).obj
          ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
            (isEtale_pairFst B S hS Yi f hf i j)).obj Z)))),
      (τ j).hom.val.app
          (.op ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))
          (M.val.map (pairChartConnect B S hS Yi f hf Z).op σ) =
        etaleSect B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j) (D.F j) Z
          ((D.transition i j).hom.val.app (.op Z)
            (etaleSectInv B S hS (pairFst B S hS Yi f i j)
              (isEtale_pairFst B S hS Yi f hf i j) (D.F i) Z
              ((τ i).hom.val.app
                (.op ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
                  (isEtale_pairFst B S hS Yi f hf i j)).obj Z)) σ))))
    (i j : I) :
    (modulePullback B S hS (pairFst B S hS Yi f i j)).map (θ i).hom ≫
        (canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
          (pair_condition B S hS Yi f i j) M).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (θ j).hom :=
  hom_ext_of_val_app B S hS
    (transition_naturality_val_of_pairReading B S hS Yi f hf D M τ θ hθ hT i j)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
