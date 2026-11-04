module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAdicDualDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSmulQuotientTower

/-!
# The offset of the two site-level adic quotient towers, and the pigeonhole at a coefficient

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `ℱ` an arbitrary sheaf of
`𝒪`-modules. There are two towers of adic quotients of `ℱ`, differing by an index shift:

* `Stacks.Sites.adicQuotientTowerOn ℐ ℱ`, whose `n`-th term is `ℱ/ℐⁿ⁺¹ℱ`, which the Koszul
  pigeonhole of `KoszulAdicQuotientSite.lean` compares the top Koszul cohomology sheaves with;
* `Stacks.Sites.idealSmulQuotientTower ℱ ℐ`, whose `n`-th term is `ℱ/ℐⁿℱ`, which is the tower
  part (3) of [Stacks, Tag 0A0K] is about and which `Completion/AdicQuotientSliceTower.lean`
  identifies the restriction of a scheme's adic quotient tower with.

The terms agree on the nose one index apart — `Stacks.Sites.idealPowSmul` is *defined* as
`idealSmul (idealPow …)`, so `ℱ/ℐⁿ⁺¹ℱ` in the first spelling and `ℱ/ℐⁿ⁺¹ℱ` in the second are one
term — but the two towers are **not** isomorphic as `ℕᵒᵖ`-functors: at `n = 0` one is `ℱ/ℐℱ` and
the other `ℱ/ℐ⁰ℱ = ℱ/ℱ = 0`, since `Stacks.Sites.idealPow_zero` gives `ℐ⁰ = 𝒪`. What relates them
is the interleaving natural transformation induced by `ℐⁿ⁺¹ ⊆ ℐⁿ`, which has inverses one level
up and is therefore a pro-isomorphism in the sense
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` consumes.

This file builds that transformation, and then states the Koszul pigeonhole at an arbitrary
coefficient with a named comparison, its cone identity and its sign-twisted form.

## Main definitions and results

* `Stacks.Sites.adicQuotientTowerOnOffset` — **the interleaving `ℱ/ℐⁿ⁺¹ℱ ⟶ ℱ/ℐⁿℱ`**, as a
  morphism of towers.
* `Stacks.Sites.adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp` — it carries the quotient
  projection `ℱ ⟶ ℱ/ℐⁿ⁺¹ℱ` to the quotient projection `ℱ ⟶ ℱ/ℐⁿℱ`. This is what pins it: two
  quotients of one sheaf of modules are identified over it exactly when the identification
  respects the projections.
* `Stacks.Sites.hasEventualInverses_adicQuotientTowerOnOffset` — **it has eventual inverses**, at
  the level above: the backward map at level `n` from level `n + 1` is the identity, both towers
  having `ℱ/ℐⁿ⁺¹ℱ` there.
* `AlgebraicGeometry.RingedSite.koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn`
  — **the cone of the Koszul pigeonhole at an arbitrary coefficient**: the canonical map
  `ℱ ⟶ H^r(K^n ⊗ ℱ)` followed by the pigeonhole comparison is the quotient projection
  `ℱ ⟶ ℱ/ℐⁿ⁺¹ℱ`.
* `AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSignedOn` — the pigeonhole
  comparison at an arbitrary coefficient, at an arbitrary spelling of the top degree and twisted
  by the sign `(-1)^r` of the Koszul self-duality, with
  `AlgebraicGeometry.RingedSite`
  `.zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSignedOn` and
  `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulTopHomologyToAdicQuotientSignedOn`.

## Implementation notes

`RingedSite.exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn` gives the
pigeonhole at an arbitrary coefficient, with no hypothesis, but it binds the comparison
existentially, and a comparison with no name has no cone identity. Pinning the projections of a
derived-limit presentation needs that identity, so the comparison has to be named at the degree
spelling `(r : ℤ)` the tower `AlgebraicGeometry.RingedSite.koszulTopHomologySystem` is taken at,
and the sign the Koszul self-duality contributes has to be carried.

The three statements are the coefficient-ful readings of statements at `ℱ = 𝒪`:
`AlgebraicGeometry.RingedSite.koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp`,
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned` and
`RingedSite.zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSigned` of
`KoszulAdicReductionIdentity.lean`. The coefficient-free ones land in
`AlgebraicGeometry.RingedSite.adicQuotientTower`, the tower of the powers `ℐⁿ⁺¹` themselves, rather
than in `Stacks.Sites.adicQuotientTowerOn` at `ℱ = 𝒪`; the two are identified by
`AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHom`, and that identification is why the
coefficient-free statements cannot simply be instantiated.

The cone identity itself is two rewrites: the canonical map onto the top cohomology sheaf is the
inclusion of the unique top-degree factor followed by
`HomologicalComplex.topToHomology` (`koszulToTopHomologyOn_eq`), the pigeonhole comparison is the
projection onto that same factor followed by the quotient projection, descended
(`topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn`), and the inclusion and the projection
cancel (`koszulTopTermInj_comp_koszulTopTermProj`), as in the proof of
`AlgebraicGeometry.RingedSite`
`.adicQuotientToKoszulTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn`.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
  Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (ℱ : AlgebraicGeometry.RingedSite.Modules.{u, u, u} X)
  (I : IdealSubsheaf.{u, u, u} X.O)

/-! ### The interleaving of the two towers -/

/-- **The interleaving `ℱ/ℐⁿ⁺¹ℱ ⟶ ℱ/ℐⁿℱ` at one level**: the map on quotients induced by the
containment `ℐⁿ⁺¹ℱ ⊆ ℐⁿℱ`.

The source is the `n`-th term of `Stacks.Sites.adicQuotientTowerOn` and the target the `n`-th term
of `Stacks.Sites.idealSmulQuotientTower`; the type is written through the two towers rather than
through the cokernels they are built from, so that the composites downstream are formed at one
spelling, as `AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHomApp` is. -/
def adicQuotientTowerOnOffsetApp (n : ℕ) :
    (adicQuotientTowerOn I ℱ).obj (op n) ⟶ (idealSmulQuotientTower ℱ I).obj (op n) :=
  Stacks.SheafOfModules.Submodule.quotientMapOfLE
    (idealPowSmul_antitone (M := ℱ) I ⊤ (Nat.le_succ n))

/-- **The interleaving carries the projection of `ℱ` onto `ℱ/ℐⁿ⁺¹ℱ` to its projection onto
`ℱ/ℐⁿℱ`.** -/
@[reassoc]
theorem adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp (n : ℕ) :
    adicQuotientTowerOnπ I ℱ n ≫ adicQuotientTowerOnOffsetApp ℱ I n =
      idealSmulQuotientπ ℱ (idealPow (O := X.O) I n) :=
  Stacks.SheafOfModules.Submodule.π_comp_quotientMapOfLE
    (idealPowSmul_antitone (M := ℱ) I ⊤ (Nat.le_succ n))

/-- **The interleaving natural transformation
`Stacks.Sites.adicQuotientTowerOn ℐ ℱ ⟶ Stacks.Sites.idealSmulQuotientTower ℱ ℐ`.**

Naturality is checked on the successor steps only, which is what `CategoryTheory.NatTrans`
`.ofOpSequence` asks for — `Stacks.Sites.idealSmulQuotientTower` is built by
`CategoryTheory.Functor.ofOpSequence` and has no description of its transition maps at a general
step — and there after cancelling the epimorphism `Stacks.Sites.adicQuotientTowerOnπ`, which
reduces both legs of the square to the projection of `ℱ` onto `ℱ/ℐⁿℱ`. -/
def adicQuotientTowerOnOffset : adicQuotientTowerOn I ℱ ⟶ idealSmulQuotientTower ℱ I :=
  NatTrans.ofOpSequence (adicQuotientTowerOnOffsetApp ℱ I) fun n => by
    refine (cancel_epi (adicQuotientTowerOnπ I ℱ (n + 1))).1 ?_
    have hL : adicQuotientTowerOnπ I ℱ (n + 1) ≫
        (adicQuotientTowerOn I ℱ).map (homOfLE (n.le_add_right 1)).op ≫
          adicQuotientTowerOnOffsetApp ℱ I n =
        idealSmulQuotientπ ℱ (idealPow (O := X.O) I n) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ adicQuotientTowerOnOffsetApp ℱ I n)
            (adicQuotientTowerOnπ_comp_map I ℱ (Nat.le_succ n))).trans
          (adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp ℱ I n))
    have hR : adicQuotientTowerOnπ I ℱ (n + 1) ≫
        adicQuotientTowerOnOffsetApp ℱ I (n + 1) ≫
          (idealSmulQuotientTower ℱ I).map (homOfLE (n.le_add_right 1)).op =
        idealSmulQuotientπ ℱ (idealPow (O := X.O) I n) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ (idealSmulQuotientTower ℱ I).map
              (homOfLE (n.le_add_right 1)).op)
            (adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp ℱ I (n + 1))).trans
          (idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ ℱ I n))
    exact hL.trans hR.symm

/-- The components of the interleaving. -/
theorem adicQuotientTowerOnOffset_app (n : ℕ) :
    (adicQuotientTowerOnOffset ℱ I).app (op n) = adicQuotientTowerOnOffsetApp ℱ I n :=
  rfl

/-- **The interleaving carries the projection of `ℱ` onto `ℱ/ℐⁿ⁺¹ℱ` to its projection onto
`ℱ/ℐⁿℱ`**, read at the components of the natural transformation. -/
@[reassoc]
theorem adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffset_app (n : ℕ) :
    adicQuotientTowerOnπ I ℱ n ≫ (adicQuotientTowerOnOffset ℱ I).app (op n) =
      idealSmulQuotientπ ℱ (idealPow (O := X.O) I n) :=
  adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp ℱ I n

/-- **The interleaving has eventual inverses**, at the level immediately above: both towers have
`ℱ/ℐⁿ⁺¹ℱ` at index `n + 1` and `n` respectively — one term, `Stacks.Sites.idealPowSmul` being
defined as `idealSmul (idealPow …)` — so the backward map may be taken to be the identity there.

The two composites are then the two transition maps of the one step `n ≤ n + 1`, which is exactly
what `NoetherianAdicCompletion.HasEventualInverses` asks for. Both are checked after cancelling
`Stacks.Sites.adicQuotientTowerOnπ`, the projections of `ℱ` being epimorphisms. -/
theorem hasEventualInverses_adicQuotientTowerOnOffset :
    NoetherianAdicCompletion.HasEventualInverses (adicQuotientTowerOnOffset ℱ I) := by
  intro n
  refine ⟨n + 1, Nat.le_succ n, 𝟙 _, ?_, ?_⟩
  · refine (cancel_epi (adicQuotientTowerOnπ I ℱ (n + 1))).1 ?_
    have hL : adicQuotientTowerOnπ I ℱ (n + 1) ≫
        (adicQuotientTowerOnOffset ℱ I).app (op (n + 1)) ≫ 𝟙 _ =
        idealSmulQuotientπ ℱ (idealPow (O := X.O) I (n + 1)) :=
      (congrArg (fun g => adicQuotientTowerOnπ I ℱ (n + 1) ≫ g)
          (Category.comp_id ((adicQuotientTowerOnOffset ℱ I).app (op (n + 1))))).trans
        (adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp ℱ I (n + 1))
    exact hL.trans (adicQuotientTowerOnπ_comp_map I ℱ (Nat.le_succ n)).symm
  · refine (cancel_epi (adicQuotientTowerOnπ I ℱ n)).1 ?_
    have hL : adicQuotientTowerOnπ I ℱ n ≫
        𝟙 _ ≫ (adicQuotientTowerOnOffset ℱ I).app (op n) =
        idealSmulQuotientπ ℱ (idealPow (O := X.O) I n) :=
      (congrArg (fun g => adicQuotientTowerOnπ I ℱ n ≫ g)
          (Category.id_comp ((adicQuotientTowerOnOffset ℱ I).app (op n)))).trans
        (adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffsetApp ℱ I n)
    exact hL.trans
      (idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ ℱ I n).symm

end Stacks.Sites

namespace AlgebraicGeometry.RingedSite

open Stacks.Sites

attribute [local instance]
  hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-! ### The cone of the Koszul pigeonhole at an arbitrary coefficient -/

/-- **The canonical map onto the top Koszul cohomology sheaf, followed by the pigeonhole
comparison, is the quotient projection `ℱ ⟶ ℱ/ℐⁿ⁺¹ℱ`** — at an arbitrary coefficient sheaf.

Both are read off the unique top-degree factor of the Koszul complex: the canonical map is the
inclusion of that factor followed by `HomologicalComplex.topToHomology`, and the pigeonhole
comparison is the projection onto that same factor followed by the quotient projection,
descended along `HomologicalComplex.topToHomology`. The inclusion and the projection cancel.

`AlgebraicGeometry.RingedSite.koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientApp` is
the same statement at `ℱ = 𝒪`, landing in `AlgebraicGeometry.RingedSite.adicQuotientTowerπ`
instead; the two towers at `ℱ = 𝒪` are identified by
`AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHom`, so neither statement is an instance of
the other. -/
theorem koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn (n : ℕ) :
    koszulToTopHomologyOn X f M n ≫ koszulTopHomologyToAdicQuotientAppOn X f M n =
      Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n := by
  rw [koszulToTopHomologyOn_eq, Category.assoc,
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn,
    koszulTopTermInj_comp_koszulTopTermProj_assoc]

/-- Twisting both factors of a composite by the same sign `(-1)^k` leaves it unchanged. -/
private theorem zsmul_neg_one_pow_comp_zsmul_neg_one_pow {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (k : ℕ) (f : A ⟶ B) (g : B ⟶ D) :
    ((-1 : ℤ) ^ k • f) ≫ ((-1 : ℤ) ^ k • g) = f ≫ g := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, neg_one_pow_mul_neg_one_pow,
    one_smul]

section Transported

variable [HasWeakSheafify X.J CommRingCat.{u}]

/-- **The Koszul pigeonhole at an arbitrary coefficient, at an arbitrary spelling of the top
degree.** The tower of `AlgebraicGeometry.RingedSite.koszulTopHomologySystem` is taken in degree
`r`, while the index type of the top-degree term of the Koszul complex carries the degree in the
spelling `r - 1 + 1`; the two integers are equal, and the comparison transports along that
equality.

`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientAt` is the same transport at
`ℱ = 𝒪`. -/
def koszulTopHomologyToAdicQuotientAtOn (p : ℤ) (hp : koszulTopDeg r = p) :
    koszulDualSystemOn X f M ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) p ⟶
      Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M :=
  hp ▸ koszulTopHomologyToAdicQuotientOn X f M

/-- The cone of the transported pigeonhole comparison. -/
theorem koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientAtOn
    (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    koszulToTopHomologyAt X f M p hp n ≫
        (koszulTopHomologyToAdicQuotientAtOn X f M p hp).app (op n) =
      Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n := by
  subst hp
  exact koszulToTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn X f M n

/-- The transported pigeonhole comparison has eventual inverses. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotientAtOn
    (p : ℤ) (hp : koszulTopDeg r = p) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToAdicQuotientAtOn X f M p hp) := by
  subst hp
  exact hasEventualInverses_koszulTopHomologyToAdicQuotientOn X f M

/-- **The Koszul pigeonhole at an arbitrary coefficient, twisted by the sign of the Koszul
self-duality.** The degree-zero component of the self-duality multiplies the unique top-degree
factor by `(-1)^r` (`AlgebraicGeometry.RingedSite.dualSign_univ`), so it is this twisted form
whose composite with the cone of the pinned Koszul presentation
(`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_eq`) is the
quotient projection on the nose.

`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientSigned` is the same twist at
`ℱ = 𝒪`. -/
def koszulTopHomologyToAdicQuotientSignedOn (p : ℤ) (hp : koszulTopDeg r = p) :
    koszulDualSystemOn X f M ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) p ⟶
      Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M :=
  (-1 : ℤ) ^ r • koszulTopHomologyToAdicQuotientAtOn X f M p hp

/-- The components of the twisted pigeonhole comparison. -/
theorem koszulTopHomologyToAdicQuotientSignedOn_app (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    (koszulTopHomologyToAdicQuotientSignedOn X f M p hp).app (op n) =
      (-1 : ℤ) ^ r • (koszulTopHomologyToAdicQuotientAtOn X f M p hp).app (op n) :=
  NatTrans.app_zsmul _ _ _

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The canonical map onto the top Koszul cohomology sheaf, twisted by the sign, followed by
the twisted pigeonhole comparison, is the quotient projection `ℱ ⟶ ℱ/ℐⁿ⁺¹ℱ`.** The two signs
multiply to one. -/
theorem zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSignedOn
    (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f M p hp n) ≫
        (koszulTopHomologyToAdicQuotientSignedOn X f M p hp).app (op n) =
      Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n := by
  rw [koszulTopHomologyToAdicQuotientSignedOn_app,
    zsmul_neg_one_pow_comp_zsmul_neg_one_pow,
    koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientAtOn]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- The twisted pigeonhole comparison has eventual inverses: those of the untwisted one, twisted
by the same sign. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotientSignedOn
    (p : ℤ) (hp : koszulTopDeg r = p) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToAdicQuotientSignedOn X f M p hp) := by
  intro n
  obtain ⟨m, hm, s, h1, h2⟩ :=
    hasEventualInverses_koszulTopHomologyToAdicQuotientAtOn X f M p hp n
  refine ⟨m, hm, (-1 : ℤ) ^ r • s, ?_, ?_⟩
  · rw [koszulTopHomologyToAdicQuotientSignedOn_app, zsmul_neg_one_pow_comp_zsmul_neg_one_pow, h1]
  · rw [koszulTopHomologyToAdicQuotientSignedOn_app, zsmul_neg_one_pow_comp_zsmul_neg_one_pow, h2]

/-! ### The comparison of the Koszul top-cohomology tower with the tower `n ↦ ℱ/ℐⁿℱ` -/

/-- **The comparison of the tower of Koszul top cohomology sheaves of `ℱ` with the tower
`n ↦ ℱ/ℐⁿℱ`**, at an arbitrary coefficient, at an arbitrary spelling of the top degree and
twisted by the sign of the Koszul self-duality: the twisted pigeonhole comparison into
`Stacks.Sites.adicQuotientTowerOn`, followed by the interleaving of the two adic quotient towers.

This is the single comparison the Koszul presentation of `ℱ^∧` is transported along to reach the
tower part (3) of [Stacks, Tag 0A0K] is about. The two factors are composed here rather than at
the consumer so that one application of
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` suffices and
the transported projections need no reassociation. -/
def koszulTopHomologyToIdealSmulQuotientTower (p : ℤ) (hp : koszulTopDeg r = p) :
    koszulDualSystemOn X f M ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) p ⟶
      Stacks.Sites.idealSmulQuotientTower (X := X) M (generatedIdealSheaf f) :=
  koszulTopHomologyToAdicQuotientSignedOn X f M p hp ≫
    Stacks.Sites.adicQuotientTowerOnOffset (X := X) M (generatedIdealSheaf f)

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The comparison has eventual inverses**: both factors do — the pigeonhole by the Artin–Rees
containments `ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ ⊆ ℐⁿ⁺¹ℱ`, the interleaving at the level
immediately above — and `NoetherianAdicCompletion.HasEventualInverses.comp` composes them. -/
theorem hasEventualInverses_koszulTopHomologyToIdealSmulQuotientTower
    (p : ℤ) (hp : koszulTopDeg r = p) :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToIdealSmulQuotientTower X f M p hp) :=
  (hasEventualInverses_koszulTopHomologyToAdicQuotientSignedOn X f M p hp).comp
    (Stacks.Sites.hasEventualInverses_adicQuotientTowerOnOffset M (generatedIdealSheaf f))

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The cone of the comparison**: the canonical map `ℱ ⟶ H^r(K^n ⊗ ℱ)` twisted by the sign,
followed by the comparison, is the quotient projection `ℱ ⟶ ℱ/ℐⁿℱ`. The two signs multiply to
one, and the interleaving carries the projection onto `ℱ/ℐⁿ⁺¹ℱ` to the projection onto
`ℱ/ℐⁿℱ`. -/
theorem zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToIdealSmulQuotientTower
    (p : ℤ) (hp : koszulTopDeg r = p) (n : ℕ) :
    ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f M p hp n) ≫
        (koszulTopHomologyToIdealSmulQuotientTower X f M p hp).app (op n) =
      Stacks.Sites.idealSmulQuotientπ (X := X) M
        (Stacks.Sites.idealPow (O := X.O) (generatedIdealSheaf f) n) := by
  refine Eq.trans (congrArg
    (fun g => ((-1 : ℤ) ^ r • koszulToTopHomologyAt X f M p hp n) ≫ g)
    (NatTrans.comp_app (koszulTopHomologyToAdicQuotientSignedOn X f M p hp)
      (Stacks.Sites.adicQuotientTowerOnOffset (X := X) M (generatedIdealSheaf f)) (op n))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToAdicQuotientSignedOn X f M p hp n) _) ?_
  exact Stacks.Sites.adicQuotientTowerOnπ_comp_adicQuotientTowerOnOffset_app M
    (generatedIdealSheaf f) n

section Pinned

open CategoryTheory.AlternatingCech

attribute [local instance 100000] HasDerivedCategory.standard

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules hasSheafCompose_forget₂_ringCat

/-- **The cone of the Koszul presentation of `ℱ^∧` over the tower `n ↦ ℱ/ℐⁿℱ`, computed.** The
Čech completion map `ℱ[0] ⟶ ℱ^∧` followed by the `n`-th projection of
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion`, carried
along `AlgebraicGeometry.RingedSite.koszulTopHomologyToIdealSmulQuotientTower`, is the quotient
projection `ℱ ⟶ ℱ/ℐⁿℱ` placed in degree zero.

**No sign survives.** The cone of the Koszul presentation carries `(-1)^r`, the dual twist of the
Koszul self-duality at the unique top-degree factor
(`AlgebraicGeometry.RingedSite.completionUnit_app_comp_koszulTopSingleProjection_eq`); the
comparison used here is twisted by the same sign, and the two multiply to one.

The composite on the left is exactly the `n`-th projection one application of
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` produces
from the Koszul presentation at
`CategoryTheory.Functor.whiskerRight (koszulTopHomologyToIdealSmulQuotientTower …)
(DerivedCategory.singleFunctor … 0)`, whose components are the images of the comparison's.

Because a map out of `ℱ^∧` into a derived-complete object is determined by its restriction along
the completion map, this identity *pins* those projections: it is what identifies them with the
canonical maps `ℱ^∧ ⟶ (ℱ/ℐⁿℱ)[0]` of part (3) of [Stacks, Tag 0A0K]. -/
theorem completionUnit_app_comp_koszulTopSingleProjection_comp_map_eq (n : ℕ) :
    (completionUnit X f).app (DerivedCategory.Q.obj (singleSheafComplex X M)) ≫
        koszulTopSingleProjection X f M n ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            ((koszulTopHomologyToIdealSmulQuotientTower X f M (r : ℤ) koszulTopDeg_eq).app
              (op n)) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.idealSmulQuotientπ (X := X) M
          (Stacks.Sites.idealPow (O := X.O) (generatedIdealSheaf f) n)) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (completionUnit_app_comp_koszulTopSingleProjection_eq X f M n) _) ?_
  refine Eq.trans
    (((DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map_comp _ _).symm) ?_
  exact congrArg
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
    (zsmul_koszulToTopHomologyAt_comp_koszulTopHomologyToIdealSmulQuotientTower X f M
      (r : ℤ) koszulTopDeg_eq n)

end Pinned

end Transported

end AlgebraicGeometry.RingedSite

end
