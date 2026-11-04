module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# Étale descent of morphisms of modules and of adic systems from the affine charts

Let `F` be an algebraic space over a scheme `S`.  The affine étale charts of `F` form a dense
subsite of its small étale site (Stacks 04JS), so a morphism of `𝒪_F`-modules is the same thing
as a family of linear maps on the sections over the affine charts, natural with respect to the
morphisms of affine charts.  This is the form of étale descent for morphisms that the proofs of
Stacks 08BB and 08BD use when they say that, by uniqueness and étale descent, *it suffices to
construct the map étale locally on the space*: the local maps, constructed over each affine
chart and unique there, are automatically natural, and they glue.

The same applies levelwise to inverse systems of `𝒪_F`-modules, in particular to the objects of
`Coh(F, 𝓘)`: a family of morphisms of modules between the terms which commutes with the
transition maps on the sections over the affine charts is a morphism of inverse systems.

## API (for the sibling work streams of the 0A01 chain; none of it is registered)

* `AlgebraicGeometry.Space.hom_ext_of_isAffineChart` — two morphisms of `𝒪_F`-modules which agree
  on the sections over every affine chart are equal.
* `AlgebraicGeometry.Space.homOfAffineCharts` — **the morphism of `𝒪_F`-modules glued from linear
  maps on the sections over the affine charts**, natural for the morphisms of affine charts, with
  `AlgebraicGeometry.Space.homOfAffineCharts_app` (its sections over an affine chart are the
  given map) and `AlgebraicGeometry.Space.eq_homOfAffineCharts` (uniqueness).
* `AlgebraicGeometry.Space.natTrans_ext_of_isAffineChart` and
  `AlgebraicGeometry.Space.natTransOfAffineCharts` — the same for morphisms of inverse systems of
  `𝒪_F`-modules, with `AlgebraicGeometry.Space.natTransOfAffineCharts_app`.
* `AlgebraicGeometry.Space.coherentAdicSystemsHomOfAffineCharts` — the same for morphisms of
  `Coh(F, 𝓘)`.

## Implementation notes

The underlying morphism of sheaves of abelian groups is
`CategoryTheory.Functor.IsCoverDense.sheafHom` for the inclusion of the affine étale charts,
which is cover dense by `AlgebraicGeometry.Space.SmallEtale.isCoverDense_affineEtaleInclusion`
and full.  Linearity over an arbitrary chart, and uniqueness, are read off on a covering of the
chart by affine charts (`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`),
using that the target is separated.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Uniqueness -/

/-- Two sections of a module over a chart are equal if they have the same restriction along every
map from an affine chart. -/
private theorem eq_of_forall_affine_map_eq {N : Modules.{u, u} B S hS F hF}
    (W : SmallEtale B S hS F) {s t : N.val.obj (op W)}
    (h : ∀ (V : SmallEtale B S hS F), IsAffine (chartScheme V) → ∀ q : V ⟶ W,
      N.val.map q.op s = N.val.map q.op t) :
    s = t := by
  obtain ⟨ι, Y, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F W
  refine N.isSheaf.isSeparated W _ hcov s t fun Z k hk => ?_
  obtain ⟨j, q, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  change N.val.map ((a j).op ≫ q.op) s = N.val.map ((a j).op ≫ q.op) t
  exact (PresheafOfModules.map_comp_apply N.val (a j).op q.op _).trans
    ((congrArg (N.val.map q.op) (h _ (haff j) (a j))).trans
      (PresheafOfModules.map_comp_apply N.val (a j).op q.op _).symm)

/-- **Two morphisms of `𝒪_F`-modules which agree on the sections over every affine chart are
equal**: every chart is covered by affine charts, and the target is separated. -/
theorem hom_ext_of_isAffineChart {M N : Modules.{u, u} B S hS F hF} {f g : M ⟶ N}
    (h : ∀ V : SmallEtale B S hS F, IsAffine (chartScheme V) →
      ∀ x : M.val.obj (op V), f.val.app (op V) x = g.val.app (op V) x) :
    f = g := by
  ext ⟨W⟩ x
  exact eq_of_forall_affine_map_eq B S hS F hF W fun V hV q =>
    ((PresheafOfModules.naturality_apply f.val q.op x).symm.trans
      (h V hV _)).trans (PresheafOfModules.naturality_apply g.val q.op x)

/-! ### Existence -/

section Glue

variable {M N : Modules.{u, u} B S hS F hF}
    (φ : ∀ V : SmallEtale B S hS F, IsAffine (chartScheme V) →
      (M.val.obj (op V) →ₗ[chartRing B S hS F hF V] N.val.obj (op V)))
    (hφ : ∀ (V W : SmallEtale B S hS F) (hV : IsAffine (chartScheme V))
      (hW : IsAffine (chartScheme W)) (f : W ⟶ V) (x : M.val.obj (op V)),
      φ W hW (M.val.map f.op x) = N.val.map f.op (φ V hV x))

/-- The given maps on the sections over the affine charts, as a morphism of the presheaves of
abelian groups restricted to the affine étale charts. -/
def affineChartsRestrictHom :
    (AffineEtale.inclusion B S hS F).op ⋙
        (M.val.presheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶
      (AffineEtale.inclusion B S hS F).op ⋙
        ((SheafOfModules.toSheaf _).obj N :
          Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj where
  app V := AddCommGrpCat.ofHom (φ V.unop.obj V.unop.property).toAddMonoidHom
  naturality V V' f := by
    ext x
    exact hφ V.unop.obj V'.unop.obj V.unop.property V'.unop.property f.unop.hom x

/-- The morphism of the underlying presheaves of abelian groups glued from the given maps. -/
def homOfAffineChartsPresheaf : M.val.presheaf ⟶ N.val.presheaf :=
  have := SmallEtale.isCoverDense_affineEtaleInclusion B S hS F hF
  Functor.IsCoverDense.sheafHom (affineChartsRestrictHom B S hS F hF φ hφ)

/-- Over an affine chart the glued morphism is the given map. -/
theorem homOfAffineChartsPresheaf_app (V : SmallEtale B S hS F) (hV : IsAffine (chartScheme V))
    (x : M.val.obj (op V)) :
    (homOfAffineChartsPresheaf B S hS F hF φ hφ).app (op V) x = φ V hV x := by
  have := SmallEtale.isCoverDense_affineEtaleInclusion B S hS F hF
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (affineChartsRestrictHom B S hS F hF φ hφ)
  exact congrArg (fun k => (k.app (op ⟨V, hV⟩)) x) h

/-- The glued morphism is linear. -/
theorem homOfAffineChartsPresheaf_smul (W : SmallEtale B S hS F)
    (r : chartRing B S hS F hF W) (m : M.val.obj (op W)) :
    (homOfAffineChartsPresheaf B S hS F hF φ hφ).app (op W) (r • m) =
      r • (homOfAffineChartsPresheaf B S hS F hF φ hφ).app (op W) m := by
  set ψ := homOfAffineChartsPresheaf B S hS F hF φ hφ
  have hnat : ∀ (V : SmallEtale B S hS F) (hV : IsAffine (chartScheme V)) (q : V ⟶ W)
      (y : M.val.obj (op W)),
      N.val.map q.op (ψ.app (op W) y) = φ V hV (M.val.map q.op y) := fun V hV q y =>
    (ConcreteCategory.congr_hom (ψ.naturality q.op) y).symm.trans
      (homOfAffineChartsPresheaf_app B S hS F hF φ hφ V hV _)
  refine eq_of_forall_affine_map_eq B S hS F hF W fun V hV q => ?_
  exact (hnat V hV q (r • m)).trans <|
    (congrArg (φ V hV) (PresheafOfModules.map_smul M.val q.op r m)).trans <|
      (map_smul (φ V hV) _ _).trans <|
        (congrArg (fun z => _ • z) (hnat V hV q m).symm).trans
          (PresheafOfModules.map_smul N.val q.op r (ψ.app (op W) m)).symm

/-- **The morphism of `𝒪_F`-modules glued from linear maps on the sections over the affine
charts**, natural with respect to the morphisms of affine charts. -/
def homOfAffineCharts : M ⟶ N :=
  ⟨PresheafOfModules.homMk (homOfAffineChartsPresheaf B S hS F hF φ hφ)
    fun X r m => homOfAffineChartsPresheaf_smul B S hS F hF φ hφ X.unop r m⟩

/-- Over an affine chart the glued morphism of `𝒪_F`-modules is the given map. -/
@[simp]
theorem homOfAffineCharts_app (V : SmallEtale B S hS F) (hV : IsAffine (chartScheme V))
    (x : M.val.obj (op V)) :
    (homOfAffineCharts B S hS F hF φ hφ).val.app (op V) x = φ V hV x :=
  homOfAffineChartsPresheaf_app B S hS F hF φ hφ V hV x

/-- **Uniqueness of the glued morphism**: a morphism whose sections over the affine charts are
the given maps is the glued morphism. -/
theorem eq_homOfAffineCharts (f : M ⟶ N)
    (hf : ∀ (V : SmallEtale B S hS F) (hV : IsAffine (chartScheme V)) (x : M.val.obj (op V)),
      f.val.app (op V) x = φ V hV x) :
    f = homOfAffineCharts B S hS F hF φ hφ :=
  hom_ext_of_isAffineChart B S hS F hF fun V hV x =>
    (hf V hV x).trans (homOfAffineCharts_app B S hS F hF φ hφ V hV x).symm

end Glue

/-! ### Inverse systems -/

/-- **Two morphisms of inverse systems of `𝒪_F`-modules which agree on the sections over every
affine chart, at every level, are equal.** -/
theorem natTrans_ext_of_isAffineChart {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} {f g : E ⟶ E'}
    (h : ∀ (n : ℕ) (V : SmallEtale B S hS F), IsAffine (chartScheme V) →
      ∀ x : (E.obj (op n)).val.obj (op V),
        (f.app (op n)).val.app (op V) x = (g.app (op n)).val.app (op V) x) :
    f = g := by
  ext ⟨n⟩ : 2
  exact hom_ext_of_isAffineChart B S hS F hF (h n)

/-- **A family of morphisms between the terms of two inverse systems of `𝒪_F`-modules which
commutes with the transition maps on the sections over the affine charts is a morphism of
inverse systems.** -/
def natTransOfAffineCharts {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (φ : ∀ n : ℕ, E.obj (op n) ⟶ E'.obj (op n))
    (hφ : ∀ (n : ℕ) (V : SmallEtale B S hS F), IsAffine (chartScheme V) →
      ∀ x : (E.obj (op (n + 1))).val.obj (op V),
        (φ n).val.app (op V) ((E.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V) x) =
          (E'.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V)
            ((φ (n + 1)).val.app (op V) x)) :
    E ⟶ E' :=
  NatTrans.ofOpSequence (fun n => φ n) fun n =>
    hom_ext_of_isAffineChart B S hS F hF fun V hV x => hφ n V hV x

/-- The levels of the morphism of inverse systems glued from a compatible family. -/
@[simp]
theorem natTransOfAffineCharts_app {E E' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (φ : ∀ n : ℕ, E.obj (op n) ⟶ E'.obj (op n))
    (hφ : ∀ (n : ℕ) (V : SmallEtale B S hS F), IsAffine (chartScheme V) →
      ∀ x : (E.obj (op (n + 1))).val.obj (op V),
        (φ n).val.app (op V) ((E.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V) x) =
          (E'.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V)
            ((φ (n + 1)).val.app (op V) x))
    (n : ℕ) :
    (natTransOfAffineCharts B S hS F hF φ hφ).app (op n) = φ n :=
  NatTrans.ofOpSequence_app _ _ (op n)

/-- **A family of morphisms between the terms of two objects of `Coh(F, 𝓘)` which commutes with
the transition maps on the sections over the affine charts is a morphism of `Coh(F, 𝓘)`.** -/
def coherentAdicSystemsHomOfAffineCharts
    {𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule}
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}
    (φ : ∀ n : ℕ, E.obj.obj (op n) ⟶ E'.obj.obj (op n))
    (hφ : ∀ (n : ℕ) (V : SmallEtale B S hS F), IsAffine (chartScheme V) →
      ∀ x : (E.obj.obj (op (n + 1))).val.obj (op V),
        (φ n).val.app (op V) ((E.obj.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V) x) =
          (E'.obj.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V)
            ((φ (n + 1)).val.app (op V) x)) :
    E ⟶ E' :=
  ObjectProperty.homMk (natTransOfAffineCharts B S hS F hF φ hφ)

end AlgebraicGeometry.Space

end
