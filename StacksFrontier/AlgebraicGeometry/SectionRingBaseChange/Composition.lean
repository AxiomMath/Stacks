module

public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.SectionPullRestrict
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.Square
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackComp
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongrNaturality

/-!
# The pullback of sections of tensor powers is functorial

Let `q : Y' ⟶ Y` and `q' : Y'' ⟶ Y'` be morphisms of schemes and `ℳ`, `ℳ'`, `ℳ''` invertible
modules on `Y`, `Y'`, `Y''` with `ε : q^*ℳ ≅ ℳ'` and `ε' : q'^*ℳ' ≅ ℳ''`. Pulling a section of
`ℳ^{⊗ n}` back along `q` and transporting it along `ε`
(`Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull`), and then pulling the result back
along `q'` and transporting it along `ε'`, is pulling the section back along `q' ≫ q` and
transporting it along the composite identification
`(q' ≫ q)^*ℳ ≅ q'^*q^*ℳ ≅ q'^*ℳ' ≅ ℳ''`. This is the composition law of the section rings
`Γ(V, 𝒪_T ⊕ ⨁_{n ≥ e} g_*ℳ^{⊗ n})` along pasted commutative squares
(`squareRingHom_comp`), which is what makes the graded algebra of sections of a polarized family
functorial in the family.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull_comp`: the composition law for
  `sectionPull`.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapApp_comp`: the degreewise maps of tail
  truncations compose.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.squareRingHom_comp`: the composition law for
  the homomorphisms of truncated section rings along pasted squares.

## Implementation notes

The proof of `sectionPull_comp` has three inputs, each already in the library: the cocycle law of
the comparison `q^*(ℳ^{⊗ n}) ≅ (q^*ℳ)^{⊗ n}` of [Stacks, Tag 01CU]
(`Stacks.AlgebraicGeometry.ProjChartIntPullbackComp.intPullIso_comp`), the naturality of that
comparison for the degreewise transport along an isomorphism
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_laurentPullback`), and the
functoriality of the degreewise transport
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_trans_hom`). The equations
are chained with `Eq.trans` and `congrArg` rather than rewritten: the two spellings of a module
over a scheme, `AlgebraicGeometry.Scheme.Modules` and the sheaves of modules over the structure
sheaf of the underlying ringed space, agree definitionally but not at the transparency at which
`rw` checks its motive.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.TensorPowerPullback RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr (congrIso)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (hom_app_inv_app)

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {Y'' Y' Y : Scheme.{u}} (q : Y' ⟶ Y) (q' : Y'' ⟶ Y')

/-- `sectionPull` spelled through `unitApp` and `Scheme.Modules.Hom.app`. -/
theorem sectionPull_eq_app (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
    (ε : (Scheme.Modules.pullback q).obj M ≅ M') (n : ℤ) (V : Y.Opens) (V' : Y'.Opens)
    (h : V' ≤ q ⁻¹ᵁ V) (s : Γ(tensorPowerModule Y M n, V)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' M'
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
    sectionPull q M M' ε n V V' h s =
      Scheme.Modules.Hom.app (X := Y') (congrIso ε n).hom V'
        ((tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n).presheaf.map (homOfLE h).op
          (Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom M n).hom
            (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule Y M n) V s))) :=
  rfl


/-- The comparison of tensor powers applied to a pulled-back section commutes with
restriction. -/
theorem intPow_unitApp_map (N : Y.Modules) [Stacks.Ample.IsInvertibleModule Y N] (n : ℤ)
    {W W' : Y.Opens} (i : W' ≤ W) (x : Γ(tensorPowerModule Y N n, W)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y N
    Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom N n).hom (q ⁻¹ᵁ W')
        (unitApp q (tensorPowerModule Y N n) W' ((tensorPowerModule Y N n).presheaf.map
          (homOfLE i).op x)) =
      (tensorPowerModule Y' ((Scheme.Modules.pullback q).obj N) n).presheaf.map
        (homOfLE (q.preimage_mono i)).op
        (Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom N n).hom (q ⁻¹ᵁ W)
          (unitApp q (tensorPowerModule Y N n) W x)) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y N
  rw [unitApp_map]
  exact hom_app_map (Z := Y') (pullbackIntPowIso q.toLRSHom.toShHom N n).hom
    (q.preimage_mono i) _

/-- The comparison of tensor powers is natural for the transport along an isomorphism. -/
theorem intPow_unitApp_congrIso {N N' : Y.Modules} [Stacks.Ample.IsInvertibleModule Y N]
    [Stacks.Ample.IsInvertibleModule Y N'] (e : N ≅ N') (n : ℤ) (W : Y.Opens)
    (x : Γ(tensorPowerModule Y N n, W)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y N
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y N'
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj N)
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj N')
    Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom N' n).hom (q ⁻¹ᵁ W)
        (unitApp q (tensorPowerModule Y N' n) W
          (Scheme.Modules.Hom.app (X := Y) (congrIso e n).hom W x)) =
      Scheme.Modules.Hom.app (X := Y') (congrIso ((Scheme.Modules.pullback q).mapIso e) n).hom
        (q ⁻¹ᵁ W)
        (Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom N n).hom (q ⁻¹ᵁ W)
          (unitApp q (tensorPowerModule Y N n) W x)) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y N
  have := isInvertible_tensorPower_of_isInvertibleModule Y N'
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj N)
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj N')
  exact (congrArg (Scheme.Modules.Hom.app (X := Y')
    (pullbackIntPowIso q.toLRSHom.toShHom N' n).hom (q ⁻¹ᵁ W))
      (unitApp_naturality q (congrIso e n).hom W x).symm).trans
    (congrArg (fun φ => Scheme.Modules.Hom.app (X := Y') φ (q ⁻¹ᵁ W)
      (unitApp q (tensorPowerModule Y N n) W x))
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_laurentPullback q e n))


open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition (compCmp) in
/-- The comparison of tensor powers along a composite, on a pulled-back section. -/
theorem intPow_unitApp_comp (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (n : ℤ)
    (V : Y.Opens) (s : Γ(tensorPowerModule Y M n, V)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback (q' ≫ q)).obj M)
    Scheme.Modules.Hom.app (X := Y'') (pullbackIntPowIso (q' ≫ q).toLRSHom.toShHom M n).hom
        ((q' ≫ q) ⁻¹ᵁ V) (unitApp (q' ≫ q) (tensorPowerModule Y M n) V s) =
      Scheme.Modules.Hom.app (X := Y'') (congrIso (compCmp q' q M) n).hom (q' ⁻¹ᵁ (q ⁻¹ᵁ V))
        (Scheme.Modules.Hom.app (X := Y'')
          (pullbackIntPowIso q'.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj M) n).hom
          (q' ⁻¹ᵁ (q ⁻¹ᵁ V))
          (unitApp q' (tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n) (q ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom M n).hom
              (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule Y M n) V s)))) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback (q' ≫ q)).obj M)
  have hcomp := Stacks.AlgebraicGeometry.ProjChartIntPullbackComp.intPullIso_comp q q' M n
  let y := unitApp q' ((Scheme.Modules.pullback q).obj (tensorPowerModule Y M n)) (q ⁻¹ᵁ V)
    (unitApp q (tensorPowerModule Y M n) V s)
  have hy := congrArg (fun φ => Scheme.Modules.Hom.app (X := Y'') φ ((q' ≫ q) ⁻¹ᵁ V) y) hcomp
  have hhom : Scheme.Modules.Hom.app (X := Y'')
      ((Scheme.Modules.pullbackComp q' q).hom.app (tensorPowerModule Y M n)) ((q' ≫ q) ⁻¹ᵁ V) y =
      unitApp (q' ≫ q) (tensorPowerModule Y M n) V s :=
    (congrArg (Scheme.Modules.Hom.app (X := Y'')
      ((Scheme.Modules.pullbackComp q' q).hom.app (tensorPowerModule Y M n)) ((q' ≫ q) ⁻¹ᵁ V))
      (Scheme.Modules.pullbackComp_inv_unit q' q (tensorPowerModule Y M n) V s).symm).trans
    (hom_app_inv_app ((Scheme.Modules.pullbackComp q' q).app (tensorPowerModule Y M n)) _ _)
  have hnat := unitApp_naturality q' (pullbackIntPowIso q.toLRSHom.toShHom M n).hom (q ⁻¹ᵁ V)
    (unitApp q (tensorPowerModule Y M n) V s)
  exact (congrArg (Scheme.Modules.Hom.app (X := Y'')
    (pullbackIntPowIso (q' ≫ q).toLRSHom.toShHom M n).hom ((q' ≫ q) ⁻¹ᵁ V)) hhom.symm).trans
    (hy.trans (congrArg (fun t => Scheme.Modules.Hom.app (X := Y'')
      (congrIso (compCmp q' q M) n).hom (q' ⁻¹ᵁ (q ⁻¹ᵁ V)) (Scheme.Modules.Hom.app (X := Y'')
        (pullbackIntPowIso q'.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj M) n).hom
        (q' ⁻¹ᵁ (q ⁻¹ᵁ V)) t)) hnat))


open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition (compCmp) in
/-- The transport along the composite identification `(q' ≫ q)^*ℳ ≅ q'^*q^*ℳ ≅ q'^*ℳ' ≅ ℳ''`,
after the composition comparison, is the transport along `q'^*ε` followed by that along `ε'`. -/
private theorem congrIso_compCmp_comp_hom (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
    (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
    (ε : (Scheme.Modules.pullback q).obj M ≅ M') (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'')
    (n : ℤ) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y'' M''
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback q').obj M')
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback (q' ≫ q)).obj M)
    (congrIso (compCmp q' q M) n).hom ≫
      (congrIso ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
        (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n).hom =
      (congrIso ((Scheme.Modules.pullback q').mapIso ε) n).hom ≫ (congrIso ε' n).hom := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y'' M''
  have := isInvertible_tensorPower_of_isInvertibleModule Y'' ((Scheme.Modules.pullback q').obj M')
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback (q' ≫ q)).obj M)
  let e₁ : (Scheme.Modules.pullback (q' ≫ q)).obj M ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M) :=
    (Scheme.Modules.pullbackComp q' q).symm.app M
  have t1 := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_trans_hom
    e₁ ((Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n
  have t2 := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_trans_hom
    (compCmp q' q M) e₁ n
  have t3 := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_trans_hom
    ((Scheme.Modules.pullback q').mapIso ε) ε' n
  have he : compCmp q' q M ≪≫ e₁ = Iso.refl _ := by
    ext : 1
    exact (Scheme.Modules.pullbackComp q' q).hom_inv_id_app M
  have t4 := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_refl_hom
    (T := Y'') ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M)) n
  have t5 := congrArg (fun e => (congrIso e n).hom) he
  refine (congrArg (fun φ => (congrIso (compCmp q' q M) n).hom ≫ φ) t1.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun φ => φ ≫ (congrIso ((Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n).hom)
    ((t2.trans t5).trans t4)).trans ?_
  exact (Category.id_comp _).trans t3.symm

/-- The iterated `sectionPull` spelled through `unitApp` and `Scheme.Modules.Hom.app`. -/
private theorem sectionPull_sectionPull_eq_app (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
    (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
    (ε : (Scheme.Modules.pullback q).obj M ≅ M') (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'')
    (n : ℤ) (V : Y.Opens) (V' : Y'.Opens) (V'' : Y''.Opens) (h : V' ≤ q ⁻¹ᵁ V)
    (h' : V'' ≤ q' ⁻¹ᵁ V') (hk : V'' ≤ q' ⁻¹ᵁ (q ⁻¹ᵁ V)) (s : Γ(tensorPowerModule Y M n, V)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y''
      ((Scheme.Modules.pullback q').obj M')
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y'' M''
    sectionPull q' M' M'' ε' n V' V'' h' (sectionPull q M M' ε n V V' h s) =
      Scheme.Modules.Hom.app (X := Y'') (congrIso ε' n).hom V''
        (Scheme.Modules.Hom.app (X := Y'') (congrIso ((Scheme.Modules.pullback q').mapIso ε) n).hom
          V'' ((tensorPowerModule Y''
            ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M)) n).presheaf.map
              (homOfLE hk).op
            (Scheme.Modules.Hom.app (X := Y'')
              (pullbackIntPowIso q'.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj M) n).hom
              (q' ⁻¹ᵁ (q ⁻¹ᵁ V))
              (unitApp q' (tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n) (q ⁻¹ᵁ V)
                (Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom M n).hom
                  (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule Y M n) V s)))))) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  have := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
  let z := Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom M n).hom
    (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule Y M n) V s)
  let t := Scheme.Modules.Hom.app (X := Y'')
    (pullbackIntPowIso q'.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj M) n).hom
    (q' ⁻¹ᵁ (q ⁻¹ᵁ V))
    (unitApp q' (tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n) (q ⁻¹ᵁ V) z)
  -- the right-hand side
  have r1 := intPow_unitApp_congrIso q' ε n V'
    ((tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n).presheaf.map (homOfLE h).op z)
  have r2 := intPow_unitApp_map q' ((Scheme.Modules.pullback q).obj M) n h z
  have r3 := hom_app_map (Z := Y'') (congrIso ((Scheme.Modules.pullback q').mapIso ε) n).hom h'
    ((tensorPowerModule Y'' ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
      n).presheaf.map (homOfLE (q'.preimage_mono h)).op t)
  have r4 := map_map_homOfLE (tensorPowerModule Y''
    ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M)) n) h'
    (q'.preimage_mono h) hk t
  refine congrArg (fun w => Scheme.Modules.Hom.app (X := Y'') (congrIso ε' n).hom V''
    ((tensorPowerModule Y'' ((Scheme.Modules.pullback q').obj M') n).presheaf.map
      (homOfLE h').op w)) (r1.trans (congrArg (fun w => Scheme.Modules.Hom.app (X := Y'')
        (congrIso ((Scheme.Modules.pullback q').mapIso ε) n).hom (q' ⁻¹ᵁ V') w) r2)) |>.trans ?_
  refine congrArg (Scheme.Modules.Hom.app (X := Y'') (congrIso ε' n).hom V'')
    r3.symm |>.trans ?_
  exact congrArg (fun w => Scheme.Modules.Hom.app (X := Y'') (congrIso ε' n).hom V''
    (Scheme.Modules.Hom.app (X := Y'') (congrIso ((Scheme.Modules.pullback q').mapIso ε) n).hom
      V'' w)) r4

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition (compCmp) in
/-- **The composition law for `sectionPull`.** -/
theorem sectionPull_comp (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
    (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
    (ε : (Scheme.Modules.pullback q).obj M ≅ M') (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'')
    (n : ℤ) (V : Y.Opens) (V' : Y'.Opens) (V'' : Y''.Opens) (h : V' ≤ q ⁻¹ᵁ V)
    (h' : V'' ≤ q' ⁻¹ᵁ V') (h'' : V'' ≤ (q' ≫ q) ⁻¹ᵁ V) (s : Γ(tensorPowerModule Y M n, V)) :
    sectionPull (q' ≫ q) M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n V V'' h'' s =
      sectionPull q' M' M'' ε' n V' V'' h' (sectionPull q M M' ε n V V' h s) := by
  have := isInvertible_tensorPower_of_isInvertibleModule Y M
  have := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
  have := isInvertible_tensorPower_of_isInvertibleModule Y''
    ((Scheme.Modules.pullback (q' ≫ q)).obj M)
  let z := Scheme.Modules.Hom.app (X := Y') (pullbackIntPowIso q.toLRSHom.toShHom M n).hom
    (q ⁻¹ᵁ V) (unitApp q (tensorPowerModule Y M n) V s)
  let t := Scheme.Modules.Hom.app (X := Y'')
    (pullbackIntPowIso q'.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj M) n).hom
    (q' ⁻¹ᵁ (q ⁻¹ᵁ V))
    (unitApp q' (tensorPowerModule Y' ((Scheme.Modules.pullback q).obj M) n) (q ⁻¹ᵁ V) z)
  have hk : V'' ≤ q' ⁻¹ᵁ (q ⁻¹ᵁ V) := h''
  -- the left-hand side
  have l1 := intPow_unitApp_comp q q' M n V s
  have l2 := hom_app_map (Z := Y'') (congrIso (compCmp q' q M) n).hom hk t
  have hL : sectionPull (q' ≫ q) M M''
      ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
        (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n V V'' h'' s =
      Scheme.Modules.Hom.app (X := Y'') ((congrIso (compCmp q' q M) n).hom ≫
        (congrIso ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n).hom) V''
        ((tensorPowerModule Y''
          ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M)) n).presheaf.map
            (homOfLE hk).op t) := by
    refine congrArg (fun w => Scheme.Modules.Hom.app (X := Y'') (congrIso
      ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
        (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n).hom V''
      ((tensorPowerModule Y'' ((Scheme.Modules.pullback (q' ≫ q)).obj M) n).presheaf.map
        (homOfLE h'').op w)) l1 |>.trans ?_
    exact congrArg (Scheme.Modules.Hom.app (X := Y'') (congrIso
      ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
        (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') n).hom V'') l2.symm
  refine hL.trans (Eq.trans ?_
    (sectionPull_sectionPull_eq_app q q' M M' M'' ε ε' n V V' V'' h h' hk s).symm)
  exact congrArg (fun φ => Scheme.Modules.Hom.app (X := Y'') φ V''
    ((tensorPowerModule Y'' ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback q).obj M))
      n).presheaf.map (homOfLE hk).op t)) (congrIso_compCmp_comp_hom q q' M M' M'' ε ε' n)


section TailComp

open Stacks.AlgebraicGeometry.SectionAlgebra

variable {T₁ T₂ T₃ : Scheme.{u}}
  {P₁ : SheafOfModules.GradedAlgebra.{u, u} T₁.ringCatSheaf}
  {P₂ : SheafOfModules.GradedAlgebra.{u, u} T₂.ringCatSheaf}
  {P₃ : SheafOfModules.GradedAlgebra.{u, u} T₃.ringCatSheaf}
  {e : ℕ} {he : 0 < e} {V₁ : T₁.Opens} {V₂ : T₂.Opens} {V₃ : T₃.Opens}

/-- **The degreewise maps of tail truncations compose.** -/
theorem tailMapApp_comp
    (ρ₁ : T₁.ringCatSheaf.obj.obj (op V₁) →+* T₂.ringCatSheaf.obj.obj (op V₂))
    (Φ₁ : ∀ n : ℤ, (P₁.piece n).val.obj (op V₁) →+ (P₂.piece n).val.obj (op V₂))
    (ρ₂ : T₂.ringCatSheaf.obj.obj (op V₂) →+* T₃.ringCatSheaf.obj.obj (op V₃))
    (Φ₂ : ∀ n : ℤ, (P₂.piece n).val.obj (op V₂) →+ (P₃.piece n).val.obj (op V₃))
    (n : ℤ) (x : (tailPiece P₁ e n).val.obj (op V₁)) :
    tailMapApp P₂ P₃ e e he he le_rfl V₂ V₃ ρ₂ Φ₂ n
        (tailMapApp P₁ P₂ e e he he le_rfl V₁ V₂ ρ₁ Φ₁ n x) =
      tailMapApp P₁ P₃ e e he he le_rfl V₁ V₃ (ρ₂.comp ρ₁) (fun m => (Φ₂ m).comp (Φ₁ m)) n x := by
  by_cases h0 : n = 0
  · rw [tailMapApp_zero h0, tailMapApp_zero h0, tailMapApp_zero h0,
      Stacks.AlgebraicGeometry.SectionAlgebra.eqToHom_app_eqToHom_app]
    rfl
  · by_cases hn : (e : ℤ) ≤ n
    · rw [tailMapApp_tail h0 hn, tailMapApp_tail h0 hn, tailMapApp_tail h0 hn,
        Stacks.AlgebraicGeometry.SectionAlgebra.eqToHom_app_eqToHom_app]
      rfl
    · exact (congrArg (tailMapApp P₂ P₃ e e he he le_rfl V₂ V₃ ρ₂ Φ₂ n)
        (tailMapApp_null h0 hn x)).trans ((map_zero _).trans (tailMapApp_null h0 hn x).symm)

end TailComp


section SquareComp

variable {Y'' Y' Y T'' T' T : Scheme.{u}} (q : Y' ⟶ Y) (q' : Y'' ⟶ Y') (g : Y ⟶ T)
  (g' : Y' ⟶ T') (g'' : Y'' ⟶ T'') (h : T' ⟶ T) (h' : T'' ⟶ T')
  (w : q ≫ g = g' ≫ h) (w' : q' ≫ g' = g'' ≫ h')
  [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  [QuasiCompact g''] [QuasiSeparated g'']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (M'' : Y''.Modules) [Stacks.Ample.IsInvertibleModule Y'' M'']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M') (ε' : (Scheme.Modules.pullback q').obj M' ≅ M'')
  (e : ℕ) (he : 0 < e) (V : T.Opens) (V' : T'.Opens) (V'' : T''.Opens)
  (hV : V' ≤ h ⁻¹ᵁ V) (hV' : V'' ≤ h' ⁻¹ᵁ V')

omit [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g'] [QuasiCompact g'']
  [QuasiSeparated g''] in
include w w' in
/-- The composite of two commutative squares commutes. -/
theorem comp_square_comm : (q' ≫ q) ≫ g = g'' ≫ (h' ≫ h) := by
  rw [Category.assoc, w, ← Category.assoc, w', Category.assoc]

include hV hV' in
/-- The composite inclusion of opens. -/
theorem le_preimage_comp : V'' ≤ (h' ≫ h) ⁻¹ᵁ V := fun _ hx => hV (hV' hx)

/-- **The homomorphisms of truncated section rings compose along pasted squares.** -/
theorem squareRingHom_comp :
    squareRingHom (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') e e he he le_rfl V V''
        (le_preimage_comp h h' V V' V'' hV hV') =
      (squareRingHom q' g' g'' h' w' M' M'' ε' e e he he le_rfl V' V'' hV').comp
        (squareRingHom q g g' h w M M' ε e e he he le_rfl V V' hV) := by
  refine DirectSum.ringHom_ext fun n a => ?_
  change squareRingHom (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') e e he he le_rfl V V''
        (le_preimage_comp h h' V V' V'' hV hV') (DirectSum.of _ n a) =
      squareRingHom q' g' g'' h' w' M' M'' ε' e e he he le_rfl V' V'' hV'
        (squareRingHom q g g' h w M M' ε e e he he le_rfl V V' hV (DirectSum.of _ n a))
  refine (squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a).trans (Eq.trans ?_
    ((congrArg (squareRingHom q' g' g'' h' w' M' M'' ε' e e he he le_rfl V' V'' hV')
      (squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a)).trans
      (squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).symm)
  refine congrArg (DirectSum.of _ n) ?_
  refine Eq.trans ?_ (tailMapApp_comp _ _ _ _ (n : ℤ) a).symm
  have hρ : ((h' ≫ h).appLE V V'' (le_preimage_comp h h' V V' V'' hV hV')).hom =
      (h'.appLE V' V'' hV').hom.comp (h.appLE V V' hV).hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have hΦ : (squarePieceMap (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') M M''
        ((Scheme.Modules.pullbackComp q' q).symm.app M ≪≫
          (Scheme.Modules.pullback q').mapIso ε ≪≫ ε') V V''
        (le_preimage_comp h h' V V' V'' hV hV')) =
      fun m => (squarePieceMap q' g' g'' h' w' M' M'' ε' V' V'' hV' m).comp
        (squarePieceMap q g g' h w M M' ε V V' hV m) := by
    funext m
    exact AddMonoidHom.ext fun x => sectionPull_comp q q' M M' M'' ε ε' m (g ⁻¹ᵁ V) (g' ⁻¹ᵁ V')
      (g'' ⁻¹ᵁ V'')
      (preimage_le_preimage q g g' h w V V' hV) (preimage_le_preimage q' g' g'' h' w' V' V'' hV')
      (preimage_le_preimage (q' ≫ q) g g'' (h' ≫ h) (comp_square_comm q q' g g' g'' h h' w w') V
        V'' (le_preimage_comp h h' V V' V'' hV hV')) x
  exact congrArg₂ (fun ρ Φ => tailMapApp _ _ e e he he le_rfl V V'' ρ Φ (n : ℤ) a) hρ hΦ

end SquareComp

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
