module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceUniversal
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Base change of the total space of a line bundle

Let `D` be a line-bundle situation: a morphism of schemes `X ⟶ S` together with an invertible
`𝒪_X`-module `L`, with total space `p : Tot(L) ⟶ X`. For a morphism of schemes `g : X' ⟶ X` the
module `g^*L` is again invertible, so `(X' ⟶ S, g^*L)` is again a line-bundle situation, and
this file proves that its total space is the fibre product of `Tot(L)` with `X'` over `X`:

`Tot_{X'}(g^*L) ≅ X' ×_X Tot_X(L)`,

as schemes over `X'`.

## Main definitions

* `Stacks.LineBundle.Situation.baseChange`: the pulled-back line-bundle situation `(X', g^*L)`.
* `Stacks.LineBundle.Situation.baseChangeToTotalSpace`: the canonical morphism
  `Tot_{X'}(g^*L) ⟶ Tot_X(L)`.
* `Stacks.LineBundle.Situation.baseChangeTotalSpaceIso`: the resulting isomorphism with the
  fibre product.

## Main results

* `Stacks.LineBundle.Situation.isPullback_baseChange`: **the base-change square is cartesian.**
  Its verticals are the two structure morphisms of the total spaces and its horizontals are the
  canonical morphism and `g`.
* `Stacks.LineBundle.Situation.baseChangeToTotalSpace_comp_totalSpaceToBase`: the square
  commutes.
* `Stacks.LineBundle.Situation.transposeEquiv`: a linear functional on `g^*L` along
  `h : W ⟶ X'` is the same thing as a linear functional on `L` along `h ≫ g`.

## Implementation notes

Everything is read off the functor of points of the total space,
`Stacks.LineBundle.Situation.totalSpaceHomEquiv`: a `W`-point of `Tot(L)` is a morphism
`k : W ⟶ X` together with a morphism of `𝒪_X`-modules `L ⟶ k_* 𝒪_W`, the morphism to the base
being `k`. A `W`-point of `Tot_{X'}(g^*L)` is thus a pair `(h : W ⟶ X', g^*L ⟶ h_* 𝒪_W)`, and
the adjunction between `g^*` and `g_*` turns the second datum into a morphism
`L ⟶ g_*(h_* 𝒪_W) = (h ≫ g)_* 𝒪_W`; that is exactly a `W`-point of `Tot(L)` lying over
`h ≫ g`, i.e. a `W`-point of the fibre product. This is
`Stacks.LineBundle.Situation.transposeEquiv`, and
`Stacks.LineBundle.Situation.transposeEquiv_comp` is its naturality in `W`, which is the
naturality of the adjunction together with the fact that the comparison
`g_*(h_* 𝒪_W) ⟶ (h ≫ g)_* 𝒪_W` of
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` is the identity on sections.

The tautological point `Stacks.LineBundle.Situation.tautologicalMap` is the universal algebra
map of the relative spectrum read on the degree-one summand; every point of the total space is
its pullback (`Stacks.LineBundle.Situation.totalSpaceHomEquiv_eq`), which is what turns the
pointwise bijection into a statement about a single comparison morphism.

Associativity of composition of morphisms of schemes holds by `rfl`, so no transport along it
is needed in the dependent sums of pairs appearing below.

Everything here is stated for an arbitrary situation. The line bundle `L(M) = Tot(M^{⊗ -1})` of
an invertible module is the case `D = Stacks.LineBundle.inverseSituation Y M`, where the
base-changed situation carries `g^*(M^{⊗ -1})` and the line bundle of `g^*M` carries
`(g^*M)^{⊗ -1}`; the comparison of those two modules, and the specialized statements it
produces, are in
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.InverseSituationBaseChange`.

## References

* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.LineBundle

/-- The canonical comparison morphism `k_* 𝒪_W ⟶ (a ≫ k)_* 𝒪_{W'}` of `𝒪_Z`-modules attached to
`a : W' ⟶ W` and `k : W ⟶ Z`. -/
def structureComparison {Z W W' : Scheme.{u}} (k : W ⟶ Z) (a : W' ⟶ W) :
    (Scheme.Modules.pushforward k).obj (SheafOfModules.unit W.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward (a ≫ k)).obj (SheafOfModules.unit W'.ringCatSheaf) :=
  AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMapAux k a)

/-- The comparison morphisms are compatible with the identification
`g_*(h_* 𝒪_W) = (h ≫ g)_* 𝒪_W`: both sides are `a` read on sections over the preimage of an
open of the base. -/
theorem pushforwardComp_structureComparison {Z X' W W' : Scheme.{u}} (g : X' ⟶ Z) (h : W ⟶ X')
    (a : W' ⟶ W) :
    (Scheme.Modules.pushforward g).map (structureComparison h a) ≫
        ((Scheme.Modules.pushforwardComp (a ≫ h) g).app
          (SheafOfModules.unit W'.ringCatSheaf)).hom =
      ((Scheme.Modules.pushforwardComp h g).app (SheafOfModules.unit W.ringCatSheaf)).hom ≫
        structureComparison (h ≫ g) a := rfl

variable (D : Situation.{u})

/-- **The tautological linear functional on `L`**: the universal algebra map of the relative
spectrum, read as a morphism `L ⟶ p_* 𝒪_{Tot(L)}` through the universal property of the
symmetric algebra. Every point of `Tot(L)` is a pullback of it. -/
def Situation.tautologicalMap :
    D.L ⟶ (Scheme.Modules.pushforward D.totalSpaceToBase).obj
      (SheafOfModules.unit D.totalSpace.ringCatSheaf) :=
  D.algebraPairEquiv D.totalSpaceToBase (universalAlgebraMap D.relativeSpecSituation)

/-- **Every point of the total space is a pullback of the tautological one.** -/
theorem Situation.totalSpaceHomEquiv_eq {W : Scheme.{u}} (l : W ⟶ D.totalSpace) :
    D.totalSpaceHomEquiv W l =
      ⟨l ≫ D.totalSpaceToBase,
        D.tautologicalMap ≫ structureComparison D.totalSpaceToBase l⟩ :=
  congrArg
    (fun x => (⟨l ≫ D.totalSpaceToBase, x⟩ :
      Σ k : W ⟶ D.X, (D.L ⟶ (Scheme.Modules.pushforward k).obj
        (SheafOfModules.unit W.ringCatSheaf))))
    (D.algebraPairEquiv_comp l D.totalSpaceToBase (universalAlgebraMap D.relativeSpecSituation))

/-- Naturality of the functor of points in the test scheme, with the point of the source
written out. -/
theorem Situation.totalSpaceHomEquiv_comp_of_eq {W Y : Scheme.{u}} (a : W ⟶ Y)
    (f : Y ⟶ D.totalSpace) (k : Y ⟶ D.X)
    (φ : D.L ⟶ (Scheme.Modules.pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))
    (hf : D.totalSpaceHomEquiv Y f = ⟨k, φ⟩) :
    D.totalSpaceHomEquiv W (a ≫ f) = ⟨a ≫ k, φ ≫ structureComparison k a⟩ := by
  rw [D.totalSpaceHomEquiv_comp a f, hf]
  rfl

variable {X' : Scheme.{u}} (g : X' ⟶ D.X)

/-- **The pulled-back line-bundle situation** `(X' ⟶ S, g^*L)`. -/
def Situation.baseChange : Situation.{u} where
  X := X'
  S := D.S
  f := g ≫ D.f
  L := (Scheme.Modules.pullback g).obj D.L
  invertible :=
    @Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf X' D.X g D.L D.invertible

/-- The scheme carrying the pulled-back bundle is `X'`. -/
theorem Situation.baseChange_X : (D.baseChange g).X = X' := rfl

/-- The pulled-back bundle is `g^*L`. -/
theorem Situation.baseChange_L :
    (D.baseChange g).L = (Scheme.Modules.pullback g).obj D.L := rfl

/-- **A linear functional on `g^*L` along `h : W ⟶ X'` is a linear functional on `L` along
`h ≫ g`.** This is the adjunction between `g^*` and `g_*`, followed by the identification
`g_*(h_* 𝒪_W) = (h ≫ g)_* 𝒪_W`. -/
def Situation.transposeEquiv {W : Scheme.{u}} (h : W ⟶ X') :
    ((D.baseChange g).L ⟶
        (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) ≃
      (D.L ⟶
        (Scheme.Modules.pushforward (h ≫ g)).obj (SheafOfModules.unit W.ringCatSheaf)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv D.L _).trans
    (Iso.homToEquiv ((Scheme.Modules.pushforwardComp h g).app
      (SheafOfModules.unit W.ringCatSheaf)))

/-- The transposition, written out. -/
theorem Situation.transposeEquiv_apply {W : Scheme.{u}} (h : W ⟶ X')
    (τ : (D.baseChange g).L ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) :
    D.transposeEquiv g h τ =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv D.L _ τ ≫
        ((Scheme.Modules.pushforwardComp h g).app
          (SheafOfModules.unit W.ringCatSheaf)).hom := rfl

/-- **Transposition is natural in the test scheme.** -/
theorem Situation.transposeEquiv_comp {W W' : Scheme.{u}} (h : W ⟶ X') (a : W' ⟶ W)
    (τ : (D.baseChange g).L ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)) :
    D.transposeEquiv g (a ≫ h) (τ ≫ structureComparison h a) =
      D.transposeEquiv g h τ ≫ structureComparison (h ≫ g) a :=
  (congrArg
      (fun x => x ≫ ((Scheme.Modules.pushforwardComp (a ≫ h) g).app
        (SheafOfModules.unit W'.ringCatSheaf)).hom)
      (Adjunction.homEquiv_naturality_right
        (Scheme.Modules.pullbackPushforwardAdjunction g) (X := D.L) τ
        (structureComparison h a))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
          (fun x => ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv D.L
            ((Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf))) τ ≫ x)
          (pushforwardComp_structureComparison g h a)).trans (Category.assoc _ _ _).symm))

/-- A point of `Tot(g^*L)` as a point of `Tot(L)`. -/
def Situation.baseChangePoint {W : Scheme.{u}}
    (σ : Σ h : W ⟶ (D.baseChange g).X, ((D.baseChange g).L ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf))) :
    Σ k : W ⟶ D.X, (D.L ⟶ (Scheme.Modules.pushforward k).obj
      (SheafOfModules.unit W.ringCatSheaf)) :=
  ⟨σ.1 ≫ g, D.transposeEquiv g σ.1 σ.2⟩

/-- **The canonical morphism `Tot_{X'}(g^*L) ⟶ Tot_X(L)`**: the point of `Tot(L)` over
`Tot(g^*L)` whose morphism to the base is the projection followed by `g` and whose linear
functional is the transpose of the tautological one. -/
def Situation.baseChangeToTotalSpace : (D.baseChange g).totalSpace ⟶ D.totalSpace :=
  (D.totalSpaceHomEquiv (D.baseChange g).totalSpace).symm
    (D.baseChangePoint g
      ⟨(D.baseChange g).totalSpaceToBase, (D.baseChange g).tautologicalMap⟩)

/-- The point of `Tot(L)` defining the canonical morphism. -/
theorem Situation.totalSpaceHomEquiv_baseChangeToTotalSpace :
    D.totalSpaceHomEquiv (D.baseChange g).totalSpace (D.baseChangeToTotalSpace g) =
      ⟨(D.baseChange g).totalSpaceToBase ≫ g,
        D.transposeEquiv g (D.baseChange g).totalSpaceToBase
          (D.baseChange g).tautologicalMap⟩ :=
  (D.totalSpaceHomEquiv _).apply_symm_apply _

/-- **The base-change square commutes.** -/
theorem Situation.baseChangeToTotalSpace_comp_totalSpaceToBase :
    D.baseChangeToTotalSpace g ≫ D.totalSpaceToBase =
      (D.baseChange g).totalSpaceToBase ≫ g :=
  congrArg Sigma.fst (D.totalSpaceHomEquiv_baseChangeToTotalSpace g)

/-- **The functor of points of the canonical morphism**: composing a point of `Tot(g^*L)` with
it transposes that point. -/
theorem Situation.totalSpaceHomEquiv_comp_baseChangeToTotalSpace {W : Scheme.{u}}
    (l : W ⟶ (D.baseChange g).totalSpace) :
    D.totalSpaceHomEquiv W (l ≫ D.baseChangeToTotalSpace g) =
      D.baseChangePoint g ((D.baseChange g).totalSpaceHomEquiv W l) := by
  rw [(D.baseChange g).totalSpaceHomEquiv_eq l]
  refine (D.totalSpaceHomEquiv_comp_of_eq l _ _ _
    (D.totalSpaceHomEquiv_baseChangeToTotalSpace g)).trans ?_
  exact congrArg (Sigma.mk (l ≫ ((D.baseChange g).totalSpaceToBase ≫ g)))
    (D.transposeEquiv_comp g (D.baseChange g).totalSpaceToBase l
      (D.baseChange g).tautologicalMap).symm

/-- The functor of points of the canonical morphism, at a point written out. -/
theorem Situation.totalSpaceHomEquiv_comp_baseChangeToTotalSpace_of_eq {W : Scheme.{u}}
    (l : W ⟶ (D.baseChange g).totalSpace)
    (σ : Σ h : W ⟶ (D.baseChange g).X, ((D.baseChange g).L ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit W.ringCatSheaf)))
    (hl : (D.baseChange g).totalSpaceHomEquiv W l = σ) :
    D.totalSpaceHomEquiv W (l ≫ D.baseChangeToTotalSpace g) = D.baseChangePoint g σ := by
  rw [D.totalSpaceHomEquiv_comp_baseChangeToTotalSpace g l, hl]

/-- A point of the total space, turned back into a morphism, lies over the point's base morphism. -/
private theorem Situation.symm_totalSpaceHomEquiv_comp_totalSpaceToBase {W : Scheme.{u}} (σ) :
    (D.totalSpaceHomEquiv W).symm σ ≫ D.totalSpaceToBase = σ.1 :=
  congrArg Sigma.fst ((D.totalSpaceHomEquiv W).apply_symm_apply σ)

/-- **The universal property of the base-change square**: a morphism to `X'` and a morphism to
`Tot(L)` agreeing over `X` come from a unique morphism to `Tot_{X'}(g^*L)`. -/
theorem Situation.baseChange_universal {W : Scheme.{u}} (a : W ⟶ X') (b : W ⟶ D.totalSpace)
    (hab : b ≫ D.totalSpaceToBase = a ≫ g) :
    ∃ l : W ⟶ (D.baseChange g).totalSpace,
      l ≫ D.baseChangeToTotalSpace g = b ∧
        l ≫ (D.baseChange g).totalSpaceToBase = a ∧
        ∀ m : W ⟶ (D.baseChange g).totalSpace,
          m ≫ D.baseChangeToTotalSpace g = b →
            m ≫ (D.baseChange g).totalSpaceToBase = a → m = l := by
  obtain ⟨⟨k, φ⟩, rfl⟩ := (D.totalSpaceHomEquiv W).symm.surjective b
  rw [D.symm_totalSpaceHomEquiv_comp_totalSpaceToBase] at hab
  subst hab
  refine ⟨((D.baseChange g).totalSpaceHomEquiv W).symm ⟨a, (D.transposeEquiv g a).symm φ⟩,
    ?_, ?_, ?_⟩
  · refine (D.totalSpaceHomEquiv W).injective ?_
    rw [D.totalSpaceHomEquiv_comp_baseChangeToTotalSpace_of_eq g _ _
      (((D.baseChange g).totalSpaceHomEquiv W).apply_symm_apply _),
      (D.totalSpaceHomEquiv W).apply_symm_apply]
    exact congrArg (Sigma.mk (a ≫ g)) ((D.transposeEquiv g a).apply_symm_apply φ)
  · exact (D.baseChange g).symm_totalSpaceHomEquiv_comp_totalSpaceToBase _
  · intro m hm₁ hm₂
    obtain ⟨⟨h, τ⟩, rfl⟩ := ((D.baseChange g).totalSpaceHomEquiv W).symm.surjective m
    have hσ : (D.baseChange g).totalSpaceHomEquiv W
        (((D.baseChange g).totalSpaceHomEquiv W).symm ⟨h, τ⟩) = ⟨h, τ⟩ :=
      ((D.baseChange g).totalSpaceHomEquiv W).apply_symm_apply _
    have hha : h = a :=
      ((D.baseChange g).symm_totalSpaceHomEquiv_comp_totalSpaceToBase ⟨h, τ⟩).symm.trans hm₂
    subst hha
    have h1 := D.totalSpaceHomEquiv_comp_baseChangeToTotalSpace_of_eq g _ _ hσ
    rw [hm₁, (D.totalSpaceHomEquiv W).apply_symm_apply] at h1
    refine congrArg _ (congrArg (Sigma.mk _) ?_)
    exact (Equiv.eq_symm_apply _).mpr (sigma_mk_injective h1).symm

/-- **The base change of the total space of a line bundle is a fibre product.** The total space
of `g^*L` over `X'` is `X' ×_X Tot(L)`: the square whose verticals are the structure morphisms
of the two total spaces and whose horizontals are the canonical morphism and `g` is cartesian.

This is the line-bundle counterpart of the base change of a relative spectrum,
[Stacks, Tag 01LS]; it is proved here from the functor of points of the total space rather
than from that tag, which would need `Sym(g^*L) ≅ g^* Sym(L)`. -/
theorem Situation.isPullback_baseChange :
    IsPullback (D.baseChangeToTotalSpace g) (D.baseChange g).totalSpaceToBase
      D.totalSpaceToBase g :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (D.baseChangeToTotalSpace_comp_totalSpaceToBase g)
    (fun s => (D.baseChange_universal g s.snd s.fst s.condition).choose)
    (fun s => (D.baseChange_universal g s.snd s.fst s.condition).choose_spec.1)
    (fun s => (D.baseChange_universal g s.snd s.fst s.condition).choose_spec.2.1)
    (fun s m hm₁ hm₂ =>
      (D.baseChange_universal g s.snd s.fst s.condition).choose_spec.2.2 m hm₁ hm₂))

/-- **The total space of the pulled-back bundle is the fibre product**, as an isomorphism. -/
def Situation.baseChangeTotalSpaceIso :
    (D.baseChange g).totalSpace ≅ Limits.pullback D.totalSpaceToBase g :=
  (D.isPullback_baseChange g).isoPullback

/-- The isomorphism with the fibre product is the canonical morphism in the first coordinate. -/
theorem Situation.baseChangeTotalSpaceIso_hom_fst :
    (D.baseChangeTotalSpaceIso g).hom ≫ Limits.pullback.fst D.totalSpaceToBase g =
      D.baseChangeToTotalSpace g :=
  (D.isPullback_baseChange g).isoPullback_hom_fst

/-- **The isomorphism with the fibre product is an isomorphism over `X'`.** -/
theorem Situation.baseChangeTotalSpaceIso_hom_snd :
    (D.baseChangeTotalSpaceIso g).hom ≫ Limits.pullback.snd D.totalSpaceToBase g =
      (D.baseChange g).totalSpaceToBase :=
  (D.isPullback_baseChange g).isoPullback_hom_snd

end Stacks.LineBundle

end
