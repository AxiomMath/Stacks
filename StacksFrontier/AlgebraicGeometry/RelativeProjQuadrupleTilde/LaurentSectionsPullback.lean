module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.Laurent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

/-!
# The ring of Laurent sections along a pullback

Let `k : T' ⟶ T` be a morphism of schemes and `L` an invertible `𝒪_T`-module. The comparison
`k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of the integral tensor powers of [Stacks, Tag 01CU] carries a local
section `x` of `L^{⊗ n}` over an open `U` of `T`, pulled back to `k⁻¹U`, to a local section of
`(k^*L)^{⊗ n}`. This file proves that this is **multiplicative** on local sections and assembles
it, over the whole of `T`, into a homomorphism of graded rings

`⨁_{n ∈ ℤ} Γ(T, L^{⊗ n}) ⟶ ⨁_{n ∈ ℤ} Γ(T', (k^*L)^{⊗ n})`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.pullbackSec`: the pulled-back
  local section `x ↦ k^*x` of the Laurent algebra.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.pullbackRing`: the ring
  homomorphism on global Laurent sections.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.pullbackSec_mul`: the
  pulled-back sections multiply as the sections do.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.pullbackRing_of`: the ring
  homomorphism on a homogeneous element.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MonoidalCategory
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open RingedSpaceModuleAdjunction

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

attribute [local instance] gcommRing

variable {T' T : Scheme.{u}} (k : T' ⟶ T)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The pullback of a local section of `L^{⊗ n}`**: a section `x` over `U` of `T` gives the
section of `(k^*L)^{⊗ n}` over `k⁻¹U` that the comparison of Tag 01CU makes of `k^*x`. -/
def pullbackSec (n : ℤ) (U : (Opens T.carrier)ᵒᵖ) (x : ((laurent L).piece n).val.obj U) :
    ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece n).val.obj
      ((opensMap (ringedSpaceHom k)).op.obj U) :=
  (laurentPullback k L n).val.app _ (pullbackUnit (ringedSpaceHom k) _ U x)

/-- The multiplication of the Laurent algebra on two local sections is its multiplication
morphism on their pure tensor. -/
theorem laurentMul_tmul {X : Scheme.{u}}
    (N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) N]
    (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ) (x : ((laurent N).piece i).val.obj U)
    (y : ((laurent N).piece j).val.obj U) :
    (laurentMul N i j).val.app U (tmul X.toRingedSpace _ _ U x y) =
      ((laurent N).mul i j).app U x y :=
  (congrArg (fun φ : (laurent N).piece i ⊗ (laurent N).piece j ⟶ (laurent N).piece (i + j) =>
      φ.val.app U (tmul X.toRingedSpace _ _ U x y)) (laurent_mulSheaf_eq N i j).symm).trans
    (mulHom_tmul (laurent N) i j U x y)

/-- **The pulled-back Laurent sections multiply as the sections do.** This is the
multiplicativity `laurentPullback_mul` of the comparison of Tag 01CU, read on the pullback of a
local pure tensor. -/
theorem pullbackSec_mul (i j : ℤ) (U : (Opens T.carrier)ᵒᵖ) (x : ((laurent L).piece i).val.obj U)
    (y : ((laurent L).piece j).val.obj U) :
    ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).mul i j).app _
        (pullbackSec k L i U x) (pullbackSec k L j U y) =
      pullbackSec k L (i + j) U (((laurent L).mul i j).app U x y) := by
  have h := congrArg (fun φ => φ.val.app ((opensMap (ringedSpaceHom k)).op.obj U)
    (pullbackUnit (ringedSpaceHom k) _ U (tmul T.toRingedSpace _ _ U x y)))
    (laurentPullback_mul k L i j)
  refine (laurentMul_tmul _ i j _ _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (laurentPullback k L (i + j)).val.app _
    (pullbackUnit (ringedSpaceHom k) _ U z)) (laurentMul_tmul L i j U x y))
  refine Eq.trans ?_ (congrArg (fun z => (laurentPullback k L (i + j)).val.app _ z)
    (pullbackUnit_naturality (ringedSpaceHom k) (laurentMul L i j) U
      (tmul T.toRingedSpace _ _ U x y)))
  refine Eq.trans ?_ h
  refine congrArg (fun z => (laurentMul ((pullbackFunctor (ringedSpaceHom k)).obj L) i j).val.app _
    z) ?_
  refine (tensorHom_tmul (laurentPullback k L i) (laurentPullback k L j) _ _ _).symm.trans ?_
  exact congrArg (fun z => (laurentPullback k L i ⊗ₘ laurentPullback k L j).val.app _ z)
    (pullbackTensorComparison_pullbackUnit (ringedSpaceHom k) _ _ U x y).symm

/-- The pulled-back section of a sum is the sum of the pulled-back sections. -/
theorem pullbackSec_add (n : ℤ) (U : (Opens T.carrier)ᵒᵖ) (x y : ((laurent L).piece n).val.obj U) :
    pullbackSec k L n U (x + y) = pullbackSec k L n U x + pullbackSec k L n U y :=
  (congrArg (fun z => (laurentPullback k L n).val.app _ z)
    (pullbackUnit_add (ringedSpaceHom k) _ U x y)).trans (map_add _ _ _)

/-- The pulled-back section of a multiple is the multiple, by the image of the scalar under the
structure morphism, of the pulled-back section. -/
theorem pullbackSec_smul (n : ℤ) (U : (Opens T.carrier)ᵒᵖ)
    (r : (structureRingSheaf T.toRingedSpace).obj.obj U) (x : ((laurent L).piece n).val.obj U) :
    pullbackSec k L n U (r • x) = sharp (ringedSpaceHom k) U r • pullbackSec k L n U x :=
  (congrArg (fun z => (laurentPullback k L n).val.app _ z)
    (pullbackUnit_smul (ringedSpaceHom k) _ U r x)).trans (map_smul _ _ _)

/-- The pulled-back section commutes with restriction. -/
theorem pullbackSec_restrict (n : ℤ) {U V : (Opens T.carrier)ᵒᵖ} (e : U ⟶ V)
    (x : ((laurent L).piece n).val.obj U) :
    ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece n).val.restrictₛₗ
        ((opensMap (ringedSpaceHom k)).op.map e) (pullbackSec k L n U x) =
      pullbackSec k L n V (((laurent L).piece n).val.restrictₛₗ e x) :=
  (PresheafOfModules.restrictₛₗ_naturality_apply (laurentPullback k L n).val
      ((opensMap (ringedSpaceHom k)).op.map e) _).symm.trans
    (congrArg (fun z => (laurentPullback k L n).val.app _ z)
      (pullbackUnit_restrict (ringedSpaceHom k) _ e x))

/-- The pulled-back unit section is the unit section. -/
theorem pullbackSec_one (U : (Opens T.carrier)ᵒᵖ) :
    pullbackSec k L 0 U ((laurent L).one.eval U) =
      (laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).one.eval _ :=
  (congrArg (fun φ => φ.val.app ((opensMap (ringedSpaceHom k)).op.obj U)
      (pullbackUnit (ringedSpaceHom k) _ U (oneSec T.toRingedSpace U)))
    (laurentPullback_zero k L)).trans (pullbackUnitComparison_oneSec (ringedSpaceHom k) U)

/-- The pulled-back global section, as an additive map of the homogeneous pieces of the global
sections. -/
def pullbackSecTop (n : ℤ) :
    (laurent L).sectionsPiece (op ⊤) n →+
      (laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).sectionsPiece (op ⊤) n where
  toFun x := pullbackSec k L n (op ⊤) x
  map_zero' := (congrArg (fun z => (laurentPullback k L n).val.app _ z) (map_zero _)).trans
    (map_zero _)
  map_add' x y := pullbackSec_add k L n (op ⊤) x y

/-- **The pullback of global Laurent sections, as a homomorphism of rings.** -/
def pullbackRing :
    Ring L (op ⊤) →+* Ring ((pullbackFunctor (ringedSpaceHom k)).obj L) (op ⊤) :=
  DirectSum.toSemiring
    (fun i => (DirectSum.of
      (fun n => (laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).sectionsPiece (op ⊤) n)
        i).comp (pullbackSecTop k L i))
    (congrArg (DirectSum.of _ 0) (pullbackSec_one k L (op ⊤)))
    (fun {i j} x y => by
      change DirectSum.of _ (i + j) (pullbackSecTop k L (i + j) (((laurent L).mul i j).app _ x y)) =
        DirectSum.of _ i (pullbackSecTop k L i x) * DirectSum.of _ j (pullbackSecTop k L j y)
      rw [of_mul_of]
      exact congrArg _ (pullbackSec_mul k L i j (op ⊤) x y).symm)

/-- On a homogeneous element of degree `n`, `pullbackRing` is the pulled-back global section in
degree `n`. -/
theorem pullbackRing_of (n : ℤ) (x : (laurent L).sectionsPiece (op ⊤) n) :
    pullbackRing k L (DirectSum.of _ n x) = DirectSum.of _ n (pullbackSecTop k L n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The pulled-back unit, of the ring of global Laurent sections of the pullback. -/
abbrev pullbackUnit' (w : (Ring L (op ⊤))ˣ) :
    (Ring ((pullbackFunctor (ringedSpaceHom k)).obj L) (op ⊤))ˣ :=
  Units.map (pullbackRing k L).toMonoidHom w

/-- A ring homomorphism of Laurent sections that acts on homogeneous elements through additive maps
`g n` sends the components of the powers of a homogeneous unit of degree one to their images. -/
private theorem pw_map_unit {X X' : Scheme.{u}}
    {M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)}
    {M' : SheafOfModules.{u} (structureRingSheaf X'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) M]
    [Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf (isSheafStruct X') M']
    (f : Ring M (op ⊤) →+* Ring M' (op ⊤))
    (g : ∀ n, (laurent M).sectionsPiece (op ⊤) n →+ (laurent M').sectionsPiece (op ⊤) n)
    (hf : ∀ n x, f (DirectSum.of _ n x) = DirectSum.of _ n (g n x)) (w : (Ring M (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring M (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring M (op ⊤))ˣ) : Ring M (op ⊤)) = DirectSum.of _ (-1) τ) (n : ℤ) :
    pw (Units.map f.toMonoidHom w) n = g n (pw w n) := by
  obtain ⟨y, hy⟩ := zpow_homogeneous w hw hw' n
  have h1 : ((Units.map f.toMonoidHom w ^ n : (Ring M' (op ⊤))ˣ) : Ring M' (op ⊤)) =
      f ((w ^ n : (Ring M (op ⊤))ˣ) : Ring M (op ⊤)) := by
    rw [← map_zpow]
    rfl
  have h2 : pw w n = y := by
    change ((w ^ n : (Ring M (op ⊤))ˣ) : Ring M (op ⊤)) n = y
    rw [hy, DirectSum.of_eq_same]
  change ((Units.map f.toMonoidHom w ^ n : (Ring M' (op ⊤))ˣ) : Ring M' (op ⊤)) n = _
  rw [h1, hy, hf, DirectSum.of_eq_same, h2]

/-- A ring homomorphism of Laurent sections that acts on homogeneous elements through additive maps
preserves homogeneous elements of each degree. -/
private theorem map_homogeneous {X X' : Scheme.{u}}
    {M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)}
    {M' : SheafOfModules.{u} (structureRingSheaf X'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) M]
    [Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf (isSheafStruct X') M']
    (f : Ring M (op ⊤) →+* Ring M' (op ⊤))
    (g : ∀ n, (laurent M).sectionsPiece (op ⊤) n →+ (laurent M').sectionsPiece (op ⊤) n)
    (hf : ∀ n x, f (DirectSum.of _ n x) = DirectSum.of _ n (g n x)) (d : ℤ) {z : Ring M (op ⊤)}
    (hz : ∃ σ, z = DirectSum.of _ d σ) : ∃ σ, f z = DirectSum.of _ d σ := by
  obtain ⟨σ, rfl⟩ := hz
  exact ⟨g d σ, hf d σ⟩

/-- The homogeneous components of the powers of a pulled-back homogeneous unit of degree one are
the pulled-back components. -/
theorem pw_pullbackUnit' (w : (Ring L (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ) (n : ℤ) :
    pw (pullbackUnit' k L w) n = pullbackSecTop k L n (pw w n) :=
  pw_map_unit (pullbackRing k L) (pullbackSecTop k L) (pullbackRing_of k L) w hw hw' n

/-- The pullback of a unit that is homogeneous of degree one is homogeneous of degree one. -/
theorem pullbackUnit'_homogeneous (w : (Ring L (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ) :
    ∃ σ, (pullbackUnit' k L w : Ring ((pullbackFunctor (ringedSpaceHom k)).obj L) (op ⊤)) =
      DirectSum.of _ 1 σ :=
  map_homogeneous (pullbackRing k L) (pullbackSecTop k L) (pullbackRing_of k L) 1 hw

/-- If the inverse of a unit is homogeneous of degree `-1`, so is the inverse of its pullback. -/
theorem pullbackUnit'_inv_homogeneous (w : (Ring L (op ⊤))ˣ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ) :
    ∃ τ, (((pullbackUnit' k L w)⁻¹ : (Ring ((pullbackFunctor (ringedSpaceHom k)).obj L) (op ⊤))ˣ) :
      Ring ((pullbackFunctor (ringedSpaceHom k)).obj L) (op ⊤)) =
      DirectSum.of _ (-1) τ := by
  rw [← map_inv]
  exact map_homogeneous (pullbackRing k L) (pullbackSecTop k L) (pullbackRing_of k L) (-1) hw'

/-- The pulled-back section commutes with a transport along an equality of degrees. -/
theorem pullbackSec_eqToHom {i j : ℤ} (h : i = j) (U : (Opens T.carrier)ᵒᵖ)
    (x : ((laurent L).piece i).val.obj U) :
    (eqToHom (congrArg (laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece h)).val.app _
        (pullbackSec k L i U x) =
      pullbackSec k L j U ((eqToHom (congrArg (laurent L).piece h)).val.app U x) := by
  subst h
  rfl

/-- In degree zero the pulled-back section is the structure-sheaf comparison of the pullback. -/
theorem pullbackSec_zero (U : (Opens T.carrier)ᵒᵖ) (x : ((laurent L).piece 0).val.obj U) :
    pullbackSec k L 0 U x =
      (pullbackUnitComparison (ringedSpaceHom k)).val.app _
        (pullbackUnit (ringedSpaceHom k) _ U x) :=
  congrArg (fun φ => φ.val.app ((opensMap (ringedSpaceHom k)).op.obj U)
      (pullbackUnit (ringedSpaceHom k) _ U x)) (laurentPullback_zero k L)

variable (w : (Ring L (op ⊤))ˣ)
  (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)

include hw hw' in
/-- **The coordinate `l ↦ w^m · l` along a pullback** is the coordinate of the pulled-back unit,
read through the comparison of the Laurent pieces and the structure-sheaf comparison. -/
theorem coord_pullback (m : ℤ) :
    laurentPullback k L (-m) ≫ coord (pullbackUnit' k L w) m =
      (pullbackFunctor (ringedSpaceHom k)).map (coord w m) ≫
        pullbackUnitComparison (ringedSpaceHom k) := by
  refine pullback_hom_ext (ringedSpaceHom k) fun U y => ?_
  have e1 := coord_app (pullbackUnit' k L w) m ((opensMap (ringedSpaceHom k)).op.obj U)
    (pullbackSec k L (-m) U y)
  have e2 : ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece m).val.restrictₛₗ
        (topRes T' ((opensMap (ringedSpaceHom k)).op.obj U)) (pw (pullbackUnit' k L w) m) =
      pullbackSec k L m U (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) := by
    rw [pw_pullbackUnit' k L w hw hw' m]
    exact (congrArg (fun e => ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).piece
        m).val.restrictₛₗ e (pullbackSecTop k L m (pw w m))) (Subsingleton.elim _ _)).trans
      (pullbackSec_restrict k L m (topRes T U) (pw w m))
  have e3 := pullbackSec_mul k L m (-m) U
    (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) y
  have e4 := pullbackSec_eqToHom k L (add_neg_cancel m) U
    (((laurent L).mul m (-m)).app U (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) y)
  have e5 := pullbackSec_zero k L U
    ((eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app U
      (((laurent L).mul m (-m)).app U
        (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) y))
  have e6 := coord_app w m U y
  change (coord (pullbackUnit' k L w) m).val.app _ (pullbackSec k L (-m) U y) =
    (pullbackUnitComparison (ringedSpaceHom k)).val.app _
      (((pullbackFunctor (ringedSpaceHom k)).map (coord w m)).val.app _
        (pullbackUnit (ringedSpaceHom k) _ U y))
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (pullbackUnitComparison (ringedSpaceHom k)).val.app _ z)
    (pullbackUnit_naturality (ringedSpaceHom k) (coord w m) U y)).symm
  refine Eq.trans ?_ (congrArg (fun z => (pullbackUnitComparison (ringedSpaceHom k)).val.app _
    (pullbackUnit (ringedSpaceHom k) _ U z)) e6).symm
  refine Eq.trans ?_ e5
  refine Eq.trans ?_ e4
  refine congrArg (fun z => (eqToHom (congrArg (laurent ((pullbackFunctor (ringedSpaceHom k)).obj
    L)).piece (add_neg_cancel m))).val.app _ z) ?_
  refine Eq.trans ?_ e3
  exact congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom k)).obj L)).mul m (-m)).app _
    z (pullbackSec k L (-m) U y)) e2

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

/-! ### The ring of Laurent sections along an isomorphism of invertible modules -/

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

attribute [local instance] gcommRing

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
  (congrIso congrIso_mul congrIso_zero)

variable {T : Scheme.{u}} {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']
  (e : L ≅ L')

/-- The comparison of the Laurent pieces induced by `e` is multiplicative on local sections. -/
theorem congrIso_mul_app (i j : ℤ) (U : (Opens T.carrier)ᵒᵖ) (x : ((laurent L).piece i).val.obj U)
    (y : ((laurent L).piece j).val.obj U) :
    ((laurent L').mul i j).app U ((congrIso e i).hom.val.app U x) ((congrIso e j).hom.val.app U y) =
      (congrIso e (i + j)).hom.val.app U (((laurent L).mul i j).app U x y) := by
  have h := congrArg (fun φ => φ.val.app U (tmul T.toRingedSpace _ _ U x y)) (congrIso_mul e i j)
  refine (laurentMul_tmul L' i j U _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (congrIso e (i + j)).hom.val.app U z)
    (laurentMul_tmul L i j U x y))
  refine Eq.trans ?_ h.symm
  exact congrArg (fun z => (laurentMul L' i j).val.app U z)
    (tensorHom_tmul (congrIso e i).hom (congrIso e j).hom U x y).symm

/-- The comparison of global Laurent sections induced by `e`, on one piece. -/
def congrSecTop (n : ℤ) :
    (laurent L).sectionsPiece (op ⊤) n →+ (laurent L').sectionsPiece (op ⊤) n where
  toFun x := (congrIso e n).hom.val.app (op ⊤) x
  map_zero' := map_zero _
  map_add' x y := map_add _ x y

/-- **The ring of global Laurent sections along an isomorphism of invertible modules.** -/
def congrRing : Ring L (op ⊤) →+* Ring L' (op ⊤) :=
  DirectSum.toSemiring
    (fun i => (DirectSum.of (fun n => (laurent L').sectionsPiece (op ⊤) n) i).comp
      (congrSecTop e i))
    (congrArg (DirectSum.of _ 0) (show (CategoryStruct.id ((laurent L).piece 0)).val.app (op ⊤)
      ((laurent L).one.eval (op ⊤)) = (laurent L').one.eval (op ⊤) from rfl))
    (fun {i j} x y => by
      change DirectSum.of _ (i + j) (congrSecTop e (i + j) (((laurent L).mul i j).app _ x y)) =
        DirectSum.of _ i (congrSecTop e i x) * DirectSum.of _ j (congrSecTop e j y)
      rw [of_mul_of]
      exact congrArg _ (congrIso_mul_app e i j (op ⊤) x y).symm)

/-- On a homogeneous element of degree `n`, `congrRing e` is the comparison induced by `e` in
degree `n`. -/
theorem congrRing_of (n : ℤ) (x : (laurent L).sectionsPiece (op ⊤) n) :
    congrRing e (DirectSum.of _ n x) = DirectSum.of _ n (congrSecTop e n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The unit transported along `e`. -/
abbrev congrUnit (w : (Ring L (op ⊤))ˣ) : (Ring L' (op ⊤))ˣ :=
  Units.map (congrRing e).toMonoidHom w

/-- The homogeneous components of the powers of a transported homogeneous unit of degree one are
the transported components. -/
theorem pw_congrUnit (w : (Ring L (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ) (n : ℤ) :
    pw (congrUnit e w) n = congrSecTop e n (pw w n) :=
  pw_map_unit (congrRing e) (congrSecTop e) (congrRing_of e) w hw hw' n

/-- The transport of a unit that is homogeneous of degree one is homogeneous of degree one. -/
theorem congrUnit_homogeneous (w : (Ring L (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ) :
    ∃ σ, (congrUnit e w : Ring L' (op ⊤)) = DirectSum.of _ 1 σ :=
  map_homogeneous (congrRing e) (congrSecTop e) (congrRing_of e) 1 hw

/-- If the inverse of a unit is homogeneous of degree `-1`, so is the inverse of its transport. -/
theorem congrUnit_inv_homogeneous (w : (Ring L (op ⊤))ˣ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ) :
    ∃ τ, (((congrUnit e w)⁻¹ : (Ring L' (op ⊤))ˣ) : Ring L' (op ⊤)) = DirectSum.of _ (-1) τ := by
  rw [← map_inv]
  exact map_homogeneous (congrRing e) (congrSecTop e) (congrRing_of e) (-1) hw'

/-- **The coordinate `l ↦ w^m · l` along an isomorphism of invertible modules** is the coordinate
of the transported unit. -/
theorem coord_congr (w : (Ring L (op ⊤))ˣ)
    (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ) (m : ℤ) :
    (congrIso e (-m)).hom ≫ coord (congrUnit e w) m = coord w m := by
  ext U y
  have e1 := coord_app (congrUnit e w) m U ((congrIso e (-m)).hom.val.app U y)
  have e2 : ((laurent L').piece m).val.restrictₛₗ (topRes T U) (pw (congrUnit e w) m) =
      (congrIso e m).hom.val.app U
        (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) := by
    rw [pw_congrUnit e w hw hw' m]
    exact (PresheafOfModules.restrictₛₗ_naturality_apply (congrIso e m).hom.val (topRes T U)
      (pw w m)).symm
  have e3 := congrIso_mul_app e m (-m) U
    (((laurent L).piece m).val.restrictₛₗ (topRes T U) (pw w m)) y
  have e4 : ∀ (z : ((laurent L).piece (m + -m)).val.obj U),
      (eqToHom (congrArg (laurent L').piece (add_neg_cancel m))).val.app U
          ((congrIso e (m + -m)).hom.val.app U z) =
        (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app U z := by
    intro z
    have h : ∀ (k : ℤ) (hk : k = 0) (z : ((laurent L).piece k).val.obj U),
        (eqToHom (congrArg (laurent L').piece hk)).val.app U ((congrIso e k).hom.val.app U z) =
          (eqToHom (congrArg (laurent L).piece hk)).val.app U z := by
      rintro k rfl z
      rfl
    exact h _ (add_neg_cancel m) z
  change (coord (congrUnit e w) m).val.app U ((congrIso e (-m)).hom.val.app U y) =
    (coord w m).val.app U y
  refine e1.trans ?_
  refine Eq.trans ?_ (coord_app w m U y).symm
  refine Eq.trans ?_ (e4 _)
  refine congrArg (fun z => (eqToHom (congrArg (laurent L').piece (add_neg_cancel m))).val.app U z)
    ?_
  refine Eq.trans ?_ e3
  exact congrArg (fun z => ((laurent L').mul m (-m)).app U z
    ((congrIso e (-m)).hom.val.app U y)) e2

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

end
