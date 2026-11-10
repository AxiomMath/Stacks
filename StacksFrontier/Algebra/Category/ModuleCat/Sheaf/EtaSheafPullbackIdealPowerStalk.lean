module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackStalkBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackTerm
public import StacksFrontier.Homology.Eta.BaseChange
public import StacksFrontier.LinearAlgebra.TensorProduct.SubmoduleBaseChange

/-!
# The normalized ideal-power comparison at a stalk of a pullback is a base change

Let `f : X ⟶ Y` be a morphism of ringed spaces, `ι : I ⟶ 𝒪_Y` an invertible ideal subsheaf, `M`
a sheaf of `𝒪_Y`-modules, `x` a point of `X`, and `a` a generator of the stalk ideal
`I_{f(x)} ⊆ 𝒪_{Y,f(x)}`.  Write `b` for the image of `a` under the germ map
`𝒪_{Y,f(x)} → 𝒪_{X,x}`; assume `b` generates `(f^*I)_x`.

`Stacks.IdealTorsion.Eta.idealPowerStalkComparison` (Tag 0GT6's normalization) divides the stalk
of the `n`-th ideal power `I^{⊗ n} ⊗ M` by `a^n`, landing in the localization `(M_{f(x)})_a`.
This file proves that the comparison *downstairs* — for the pulled-back ideal `f^*I`, the
pulled-back module `f^*M` and the generator `b` — is the base change along the germ map of the
comparison upstairs.

The proof is uniqueness: `Stacks.IdealTorsion.Eta.IdealPowerStalkComparison.map_eq` says that the
three defining properties of the comparison pin it down, so it suffices to check that the
base-changed upstairs comparison has them.  All three are then unconditional facts: the zeroth
comparison is localization, consecutive comparisons differ by the ideal-power inclusion, and the
range is `b^{-n} (f^*M)_x`, which is what base change does to `a^{-n} M_{f(x)}` by
`Stacks.Eta.BaseChange.fpowSub_baseChange_eq`.  **No flatness is used anywhere.**

## Main definitions

* `Stacks.IdealTorsion.Eta.stalkLocPullback` and
  `Stacks.IdealTorsion.Eta.stalkLocBaseChange`: the two localizations at `b` in play, of the
  stalk of the pullback and of the base change of the stalk.
* `Stacks.IdealTorsion.Eta.stalkPsiMap`: the comparison
  `𝒪_{X,x} ⊗ (M_{f(x)})_a ≅ (𝒪_{X,x} ⊗ M_{f(x)})_b` of `Stacks.Eta.BaseChange.psiEquiv`, as a
  morphism of `𝒪_{X,x}`-modules.
* `Stacks.IdealTorsion.Eta.stalkLocBaseChangeInv`: the localization at `b` of the inverse of the
  comparison of Tag 0098.

## Main results

* `Stacks.IdealTorsion.Eta.psiEquiv_comp_baseChange_toLoc`: base change carries the localization
  map to the localization map.
* `Stacks.IdealTorsion.Eta.map_fLoc_fpowSub`: a surjection carries the power submodules
  `r^{-k} P ⊆ P_r` onto one another.
* `Stacks.IdealTorsion.Eta.idealPowerStalkComparison_pullback`: **the comparison downstairs is
  the base change of the comparison upstairs.**

## Implementation notes

The commutative-ring structure making `𝒪_{X,x}` an algebra over `𝒪_{Y,f(x)}` is the germ map's
`RingHom.toAlgebra`, seated by `letI`; it is not declared as an instance, since its two carriers
determine neither `f` nor `x`.

Two spellings of the base change are in play and only one of them is visible to instance search.
`Stacks.RingedSpace.commStalkBaseChange` is `ModuleCat.extendScalars`, whose value at `N` has
carrier `↑((restrictScalars φ).obj (ModuleCat.of B B)) ⊗[A] ↑N`; that is definitionally
`B ⊗[A] ↑N`, and unification — which runs at `default` transparency — crosses between the two
without trouble, but instance search does not.  So `ModuleCat.ofHom`, which synthesises the
module structure on the carrier it is handed, cannot be used to build a morphism out of such an
object.  Every morphism below is built with `CategoryTheory.ConcreteCategory.ofHom` instead,
whose source and target are the *objects* rather than their carriers.

For the same reason every step of the three field proofs is a ground equation closed by
`Eq.trans` and `congrArg` rather than a `rw`.  A rewrite has to match syntactically, and the
objects in these composites — `(f^*(I^{⊗ 0} ⊗ M))_x` against `(f^*M)_x` in degree `0`, or
`(F ⋙ G).obj N` against `G.obj (F.obj N)` — agree only definitionally; `congrArg` and `Eq.trans`
check at `default` transparency and go through where `rw` reports that it did not find the
pattern.  This is the idiom recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheaf.lean`.

## References

* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0GSR](https://stacks.math.columbia.edu/tag/0GSR)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor commStalkGermMap commStalkBaseChange
  stalkPullbackBaseChangeIso stalkPullbackBaseChangeIso_naturality)

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

open scoped TensorProduct

universe u

namespace Stacks.IdealTorsion.Eta

noncomputable section

/-! ### Two unconditional facts about localization and base change -/

section Ring

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Base change carries the localization map to the localization map.**  Composing the base
change of `N → N_a` with the comparison `B ⊗_A N_a ≅ (B ⊗_A N)_b` of
`Stacks.Eta.BaseChange.psiEquiv` gives the localization map of `B ⊗_A N` at `b`. -/
theorem psiEquiv_comp_baseChange_toLoc (r : A) (N : Type u) [AddCommGroup N] [Module A N] :
    (Stacks.Eta.BaseChange.psiEquiv r N).toLinearMap.comp
        (LinearMap.baseChange B (EtaPow.toLoc r N)) =
      EtaPow.toLoc (algebraMap A B r) (B ⊗[A] N) := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
      have hc : (c ⊗ₜ[A] (EtaPow.toLoc r N m) : B ⊗[A] EtaPow.Loc r N) =
          c • ((1 : B) ⊗ₜ[A] (EtaPow.toLoc r N m)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hbase : EtaPow.toLoc (algebraMap A B r) (B ⊗[A] N) (c ⊗ₜ[A] m) =
          c • EtaPow.toLoc (algebraMap A B r) (B ⊗[A] N) ((1 : B) ⊗ₜ[A] m) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hone : Stacks.Eta.BaseChange.etaBCPsi (B := B) r N (EtaPow.toLoc r N m) =
          EtaPow.toLoc (algebraMap A B r) (B ⊗[A] N) ((1 : B) ⊗ₜ[A] m) := by
        have h := Stacks.Eta.BaseChange.etaBCPsi_fpowMap (B := B) r N 0 m
        simpa only [EtaPow.fpowMap_apply, zpow_zero, one_smul] using h
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe]
      rw [hc, map_smul, ← Stacks.Eta.BaseChange.etaBCPsi_eq_psiEquiv, hone, hbase]
  | add z w hz hw => simp only [map_add, hz, hw]

end Ring

section Loc

variable {R : Type u} [CommRing R]

/-- **The power submodules `r^{-k} P ⊆ P_r` are carried onto one another by a surjection.** -/
theorem map_fLoc_fpowSub (r : R) {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (g : P →ₗ[R] Q) (hg : Function.Surjective g) (k : ℤ) :
    Submodule.map (EtaPow.fLoc r g) (EtaPow.fpowSub r P k) = EtaPow.fpowSub r Q k := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, rfl⟩ := EtaPow.mem_fpowSub.mp hz
    refine EtaPow.mem_fpowSub.mpr ⟨g p, ?_⟩
    rw [EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]
  · intro w hw
    obtain ⟨q, rfl⟩ := EtaPow.mem_fpowSub.mp hw
    obtain ⟨p, rfl⟩ := hg q
    exact ⟨(Stacks.GradedLaurent.awayUnit r ^ k) • EtaPow.toLoc r P p,
      EtaPow.mem_fpowSub.mpr ⟨p, rfl⟩, by rw [EtaPow.fLoc_zpow_smul, EtaPow.fLoc_toLoc]⟩

end Loc

/-! ### The comparison downstairs is the base change of the comparison upstairs -/

section Sheaf

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (x : X)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (a : ringStalk Y (f.hom.base x)) (ha : GeneratesStalkIdeal Y ι (f.hom.base x) a)
  (hb : GeneratesStalkIdeal X (pullbackIdealIncl f I ι) x (commStalkGermMap f x a))

omit [Mono ι] [Mono (pullbackIdealIncl f I ι)] in
/-- The rearranged interchange square: the ideal-power inclusion downstairs, followed by the
inverse interchange, is the inverse interchange followed by the pullback of the ideal-power
inclusion upstairs.  This is
`Stacks.IdealTorsion.Eta.map_idealPowerIncl` with the two isomorphisms moved across. -/
private theorem idealPowerIncl_comp_pullbackIdealPowerIso_inv (n : ℤ) :
    idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
          ((pullbackFunctor f).obj M) ≫ (pullbackIdealPowerIso f I n M).inv =
      (pullbackIdealPowerIso f I (n + 1) M).inv ≫
        (pullbackFunctor f).map (idealPowerIncl Y I ι n M) :=
  -- The square mixes the category instance of the pullback functor's spelling of the structure
  -- sheaf with that of the décalage files, so `rw` cannot match the iso cancellations; they are
  -- applied as terms, which elaborate at `default` transparency.
  (Iso.eq_inv_comp (pullbackIdealPowerIso f I (n + 1) M)).mpr
    ((Category.assoc _ _ _).symm.trans
      ((Iso.comp_inv_eq (pullbackIdealPowerIso f I n M)).mpr
        (map_idealPowerIncl f I ι n M).symm))

/-- The localization at `b` of the stalk at `x` of the pullback. -/
abbrev stalkLocPullback : ModuleCat.{u} (ringStalk X x) :=
  ModuleCat.of (ringStalk X x) (EtaPow.Loc (commStalkGermMap f x a)
    ((stalkModuleFunctor X x).obj ((pullbackFunctor f).obj M)))

/-- The localization at `b` of the base change of the stalk at `f x`. -/
abbrev stalkLocBaseChange : ModuleCat.{u} (ringStalk X x) :=
  ModuleCat.of (ringStalk X x) (EtaPow.Loc (commStalkGermMap f x a)
    ((commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M)))

/-- The localization at `b` of the inverse of the comparison of Tag 0098. -/
def stalkLocBaseChangeInv : stalkLocBaseChange f x M a ⟶ stalkLocPullback f x M a :=
  ConcreteCategory.ofHom (X := stalkLocBaseChange f x M a) (Y := stalkLocPullback f x M a)
    (EtaPow.fLoc (commStalkGermMap f x a)
      ((stalkPullbackBaseChangeIso f x).inv.app M).hom)

/-- The localization map of the base change, as a morphism. -/
private def toLocBaseChangeMap :
    (commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M) ⟶
      stalkLocBaseChange f x M a :=
  ConcreteCategory.ofHom
    (X := (commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M))
    (Y := stalkLocBaseChange f x M a)
    (EtaPow.toLoc (commStalkGermMap f x a)
      ((commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M)))

/-- **The comparison of the base change of a localization with the localization of the base
change** (`Stacks.Eta.BaseChange.psiEquiv`), as a morphism of `𝒪_{X,x}`-modules. -/
def stalkPsiMap :
    (commStalkBaseChange f x).obj (ModuleCat.of (ringStalk Y (f.hom.base x))
        (EtaPow.Loc a ((stalkModuleFunctor Y (f.hom.base x)).obj M))) ⟶
      stalkLocBaseChange f x M a :=
  letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
  ConcreteCategory.ofHom
    (X := (commStalkBaseChange f x).obj (ModuleCat.of (ringStalk Y (f.hom.base x))
      (EtaPow.Loc a ((stalkModuleFunctor Y (f.hom.base x)).obj M))))
    (Y := stalkLocBaseChange f x M a)
    (Stacks.Eta.BaseChange.psiEquiv a
      ((stalkModuleFunctor Y (f.hom.base x)).obj M)).toLinearMap

/-- The localization map of the stalk of the pullback, as a morphism. -/
private def toLocPullbackMap :
    (stalkModuleFunctor X x).obj ((pullbackFunctor f).obj M) ⟶ stalkLocPullback f x M a :=
  ConcreteCategory.ofHom
    (X := (stalkModuleFunctor X x).obj ((pullbackFunctor f).obj M))
    (Y := stalkLocPullback f x M a)
    (EtaPow.toLoc (commStalkGermMap f x a)
      ((stalkModuleFunctor X x).obj ((pullbackFunctor f).obj M)))

/-- The part of the candidate comparison downstairs after the interchange: compare the stalk of
the pullback with the base change of the stalk, base change the comparison upstairs, and read the
result inside `((f^*M)_x)_b`. -/
private def candTail (n : ℤ) :
    (stalkModuleFunctor X x).obj ((pullbackFunctor f).obj (idealPowerTerm Y I n M)) ⟶
      stalkLocPullback f x M a :=
  (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I n M) ≫
    (commStalkBaseChange f x).map
        ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n) ≫
      stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a

/-- The candidate comparison downstairs, in degree `n`: undo the interchange of the pullback with
the ideal power, then apply `candTail`. -/
private def candMap (n : ℤ) :
    (stalkModuleFunctor X x).obj
        (idealPowerTerm X ((pullbackFunctor f).obj I) n ((pullbackFunctor f).obj M)) ⟶
      stalkLocPullback f x M a :=
  (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).inv ≫ candTail f x I ι M a ha n

/-- **Base change carries the localization map to the localization map**, as morphisms. -/
private theorem baseChange_toLoc_comp_stalkPsiMap :
    (commStalkBaseChange f x).map (ModuleCat.ofHom
          (EtaPow.toLoc a ((stalkModuleFunctor Y (f.hom.base x)).obj M))) ≫ stalkPsiMap f x M a =
      toLocBaseChangeMap f x M a := by
  let : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
  exact ModuleCat.hom_ext <| psiEquiv_comp_baseChange_toLoc (B := ringStalk X x) a
    ((stalkModuleFunctor Y (f.hom.base x)).obj M)

/-- The localization map is natural, so localizing the inverse comparison of Tag 0098 after it is
that comparison before it. -/
private theorem toLocBaseChangeMap_comp_stalkLocBaseChangeInv :
    toLocBaseChangeMap f x M a ≫ stalkLocBaseChangeInv f x M a =
      (stalkPullbackBaseChangeIso f x).inv.app M ≫ toLocPullbackMap f x M a :=
  ModuleCat.hom_ext <| LinearMap.ext fun z =>
    EtaPow.fLoc_toLoc ((stalkPullbackBaseChangeIso f x).inv.app M).hom z

omit [Mono (pullbackIdealIncl f I ι)] in
/-- **The tail of the candidate comparison is compatible with the ideal-power inclusion.**  The
pullback of the inclusion upstairs, followed by the comparison in degree `n`, is the comparison
in degree `n + 1`: the first step is the naturality of Tag 0098 in the module
(`Stacks.RingedSpace.stalkPullbackBaseChangeIso_naturality`) and the second is the `succ` clause
of the comparison upstairs, base changed. -/
private theorem candMap_tail_succ (n : ℤ) :
    (stalkModuleFunctor X x).map ((pullbackFunctor f).map (idealPowerIncl Y I ι n M)) ≫
        candTail f x I ι M a ha n = candTail f x I ι M a ha (n + 1) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ ((commStalkBaseChange f x).map
            ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n) ≫
          stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a))
        (stalkPullbackBaseChangeIso_naturality f x (idealPowerIncl Y I ι n M))).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k =>
            (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I (n + 1) M) ≫ k)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ (stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a))
                (((commStalkBaseChange f x).map_comp
                  ((stalkModuleFunctor Y (f.hom.base x)).map (idealPowerIncl Y I ι n M))
                  ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n)).symm)).trans
              (congrArg (fun k => (commStalkBaseChange f x).map k ≫
                  (stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a))
                ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).succ n)))))))

/-- The candidate comparison downstairs.

The three fields are exactly the three unconditional facts quoted in the module docstring, and
`Stacks.IdealTorsion.Eta.IdealPowerStalkComparison.map_eq` then identifies this with the
comparison downstairs. -/
private def pullbackIdealPowerStalkComparison :
    IdealPowerStalkComparison X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
      ((pullbackFunctor f).obj M) x (commStalkGermMap f x a) where
  map n := candMap f x I ι M a ha n
  zero := by
    have h0 : (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I 0 M).inv = 𝟙 _ := by
      rw [pullbackIdealPowerIso_zero]
      exact (stalkModuleFunctor X x).map_id _
    have key : (commStalkBaseChange f x).map
            ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map 0) ≫
          stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a =
        (stalkPullbackBaseChangeIso f x).inv.app M ≫ toLocPullbackMap f x M a :=
      (congrArg (fun k => (commStalkBaseChange f x).map k ≫
            (stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a))
          (idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).zero).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ stalkLocBaseChangeInv f x M a)
              (baseChange_toLoc_comp_stalkPsiMap f x M a)).trans
            (toLocBaseChangeMap_comp_stalkLocBaseChangeInv f x M a)))
    exact (congrArg (· ≫ candTail f x I ι M a ha 0) h0).trans
      ((Category.id_comp _).trans
        ((congrArg ((stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I 0 M) ≫ ·)
            key).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ toLocPullbackMap f x M a)
              (Iso.hom_inv_id_app (stalkPullbackBaseChangeIso f x)
                (idealPowerTerm Y I 0 M))).trans
              (Category.id_comp _)))))
  succ n :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ candTail f x I ι M a ha n)
          (((stalkModuleFunctor X x).map_comp
            (idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
              ((pullbackFunctor f).obj M))
            (pullbackIdealPowerIso f I n M).inv).symm)).trans
        ((congrArg (fun k => (stalkModuleFunctor X x).map k ≫ candTail f x I ι M a ha n)
            (idealPowerIncl_comp_pullbackIdealPowerIso_inv f I ι M n)).trans
          ((congrArg (· ≫ candTail f x I ι M a ha n)
              ((stalkModuleFunctor X x).map_comp
                (pullbackIdealPowerIso f I (n + 1) M).inv
                ((pullbackFunctor f).map (idealPowerIncl Y I ι n M)))).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun k => (stalkModuleFunctor X x).map
                  (pullbackIdealPowerIso f I (n + 1) M).inv ≫ k)
                (candMap_tail_succ f x I ι M a ha n))))))
  range n := by
    let : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) := (commStalkGermMap f x).toAlgebra
    have hc : candMap f x I ι M a ha n =
        ((stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).inv ≫
            (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I n M)) ≫
          ((commStalkBaseChange f x).map
              ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n) ≫
            stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a) := (Category.assoc _ _ _).symm
    have htop : LinearMap.range
        (((stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).inv ≫
          (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I n M)).hom) = ⊤ := by
      rw [LinearMap.range_eq_top]
      -- both factors are isomorphisms; the instances are given by name, `idealPowerTerm` being
      -- indexed by a spelling of the structure sheaf that instance search does not reach from
      -- the one the pullback comparison is typed over
      exact ((ConcreteCategory.isIso_iff_bijective _).1
        (@IsIso.comp_isIso _ _ _ _ _ _ _
          ((stalkModuleFunctor X x).mapIso (pullbackIdealPowerIso f I n M).symm).isIso_hom
          ((stalkPullbackBaseChangeIso f x).app
            (idealPowerTerm Y I n M)).isIso_hom)).surjective
    have hBC : LinearMap.range (((commStalkBaseChange f x).map
          ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n)).hom) =
        Submodule.baseChange (ringStalk X x)
          (EtaPow.fpowSub a ((stalkModuleFunctor Y (f.hom.base x)).obj M) n) :=
      (ArtinReesBaseChange.range_baseChange (B := ringStalk X x)
          ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n).hom).trans
        (congrArg (Submodule.baseChange (ringStalk X x))
          ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).range n))
    have hpsi : Submodule.map (stalkPsiMap f x M a).hom
          (Submodule.baseChange (ringStalk X x)
            (EtaPow.fpowSub a ((stalkModuleFunctor Y (f.hom.base x)).obj M) n)) =
        EtaPow.fpowSub (commStalkGermMap f x a)
          ((commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M)) n :=
      ((Stacks.Eta.BaseChange.fpowSub_baseChange_eq (B := ringStalk X x) a
          ((stalkModuleFunctor Y (f.hom.base x)).obj M) n).trans
        (Stacks.Eta.BaseChange.span_image_etaBCPsi (B := ringStalk X x) a
          ((stalkModuleFunctor Y (f.hom.base x)).obj M)
          (EtaPow.fpowSub a ((stalkModuleFunctor Y (f.hom.base x)).obj M) n))).symm
    have hloc : Submodule.map (stalkLocBaseChangeInv f x M a).hom
          (EtaPow.fpowSub (commStalkGermMap f x a)
            ((commStalkBaseChange f x).obj ((stalkModuleFunctor Y (f.hom.base x)).obj M)) n) =
        EtaPow.fpowSub (commStalkGermMap f x a)
          ((stalkModuleFunctor X x).obj ((pullbackFunctor f).obj M)) n :=
      map_fLoc_fpowSub (commStalkGermMap f x a)
        ((stalkPullbackBaseChangeIso f x).inv.app M).hom
        ((ConcreteCategory.isIso_iff_bijective _).1
          ((stalkPullbackBaseChangeIso f x).app M).isIso_inv).surjective n
    rw [hc, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _ htop,
      ModuleCat.hom_comp, LinearMap.range_comp, ModuleCat.hom_comp, Submodule.map_comp,
      hBC, hpsi, hloc]

/-- **The normalized ideal-power comparison at a stalk of a pullback is the base change of the
comparison upstairs.**  Let `f : X ⟶ Y` be a morphism of ringed spaces, `ι : I ⟶ 𝒪_Y` an
invertible ideal subsheaf, `M` a sheaf of `𝒪_Y`-modules and `x` a point of `X`.  Let `a` generate
the stalk ideal `I_{f(x)}` and let its image `b` under the germ map generate `(f^*I)_x`.  Then
dividing by `b^n` at `x`, after the interchange of the pullback with the `n`-th ideal power, is
the base change along the germ map of dividing by `a^n` at `f(x)`, read inside the localization
of the base change through `Stacks.Eta.BaseChange.psiEquiv`.

**No flatness is assumed.**  The proof is uniqueness of the comparison
(`Stacks.IdealTorsion.Eta.IdealPowerStalkComparison.map_eq`): the right-hand side, precomposed
with the inverse interchange, satisfies the three defining properties, which are the
unconditional facts that base change carries the localization map to the localization map, that
the ideal-power inclusion downstairs is the pullback of the one upstairs
(`Stacks.IdealTorsion.Eta.map_idealPowerIncl`), and that base change carries `a^{-n} M_{f(x)}`
onto `b^{-n} (f^*M)_x` (`Stacks.Eta.BaseChange.fpowSub_baseChange_eq`). -/
theorem idealPowerStalkComparison_pullback (n : ℤ) :
    (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).hom ≫
        (idealPowerStalkComparison X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          ((pullbackFunctor f).obj M) x (commStalkGermMap f x a) hb).map n =
      (stalkPullbackBaseChangeIso f x).hom.app (idealPowerTerm Y I n M) ≫
        (commStalkBaseChange f x).map
            ((idealPowerStalkComparison Y I ι M (f.hom.base x) a ha).map n) ≫
          stalkPsiMap f x M a ≫ stalkLocBaseChangeInv f x M a := by
  have hm := IdealPowerStalkComparison.map_eq X ((pullbackFunctor f).obj I)
    (pullbackIdealIncl f I ι) ((pullbackFunctor f).obj M) x (commStalkGermMap f x a) hb
    (pullbackIdealPowerStalkComparison f x I ι M a ha) n
  have hidd : (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).hom ≫
      (stalkModuleFunctor X x).map (pullbackIdealPowerIso f I n M).inv =
        𝟙 ((stalkModuleFunctor X x).obj
          ((pullbackFunctor f).obj (idealPowerTerm Y I n M))) :=
    -- the goal is not type-correct at `implicit` transparency, so `rw` cannot act on it; the
    -- functor's image of the isomorphism supplies the identity directly
    ((stalkModuleFunctor X x).mapIso (pullbackIdealPowerIso f I n M)).hom_inv_id
  refine Eq.trans (congrArg (fun k => (stalkModuleFunctor X x).map
    (pullbackIdealPowerIso f I n M).hom ≫ k) hm.symm) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ candTail f x I ι M a ha n) hidd).trans (Category.id_comp _))

end Sheaf

end

end Stacks.IdealTorsion.Eta

end
