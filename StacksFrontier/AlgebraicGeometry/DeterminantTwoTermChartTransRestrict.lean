module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTrans

/-!
# The chart comparison of the determinant on the open subschemes is transitive

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ V' ≤ W` affine opens of `X`. The chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` identifies the determinant of `L` on
`V` with the *restriction* along `V ⟶ W` of the determinant of `L` on `W`, while
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso` identifies the *pullback* along
`V ⟶ W` of the determinant on `W` with the determinant on `V`. This file shows that the two are
the same comparison, and deduces from the cocycle condition on the spectra the cocycle condition
for `chartDetRestrictIso`, which is the hypothesis
`AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` asks for.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_eq` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_hom`: **the restriction form of the
  chart comparison is the pullback form**, read through
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso_trans`: **the pullback form composes
  along a chain of two inclusions**, granted the cocycle condition on the spectra.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_trans`: **the restriction form
  composes**, in exactly the shape `AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` wants.

## Implementation notes

Both comparisons are iterated `CategoryTheory.Iso.trans`es of composition and reindexing
isomorphisms of `AlgebraicGeometry.Scheme.Modules.pullback`, so every statement below is an
associativity chase, and two different obstructions stand in the way of running one on the
concrete terms.

The first is the familiar one: a single notion has two names. An inclusion of affine opens
reaches the declarations stated for arbitrary opens through
`AffineOpensGlue.coe_le_coe` in the determinant development and through
`AlgebraicGeometry.AffineOpensGlue.coe_le_coe` in the glueing datum, and `chartDet L V` is equal
to `(Scheme.Modules.pullback _).obj (chartDetSpec L V)` only by unfolding a definition. A goal
mixing two such spellings is type-correct at default transparency but not at the transparency
`simp` and `rw` check their results at, so they refuse with "did not find an occurrence of the
pattern" — `rw [CategoryTheory.Iso.trans_hom]` fails outright on the unfolded
`chartDetRestrictIso`. Every chase is therefore run in a private helper in which each scheme,
morphism, module and isomorphism is a *variable*, and the concrete terms are supplied only when
the helper is applied.

The second obstruction decides the shape of the rest of the file: some of these spelling
differences are affordable for the kernel and some are not, the kernel having a reduction budget
and no simp set. Affordable: `AlgebraicGeometry.Scheme.Modules.pullback` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` at two spellings of one morphism or module;
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` at two spellings of one morphism, *as a natural
transformation*; `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` at two spellings of one module; and
unfolding `chartDetRestrictIso` as an isomorphism. Not affordable:
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` *evaluated at* two spellings of one module;
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` under `CategoryTheory.Functor.map` at two
spellings of one morphism; and unfolding `chartDetRestrictIso` *underneath*
`CategoryTheory.Iso.hom`. Hence

* the concrete comparisons enter a helper as variables together with an *isomorphism-valued*
  `rfl` hypothesis naming their definition — `hFh : Fh = _ ≪≫ _` — and never by unfolding
  `CategoryTheory.Iso.hom`;
* the reindexing along the factorisation of `V ⟶ W` enters `restrictChase` and
  `chartDetPullbackIso_trans` as a variable natural transformation `pcg` named by `hpcg`, so that
  the module it is evaluated at is never respelled underneath it;
* every inclusion of affine opens is spelled with
  `AlgebraicGeometry.AffineOpensGlue.coe_le_coe` from the spectra upwards — the spelling the
  statement of `chartDetRestrictIso_trans` is fixed to — because it is the restriction side that
  cannot be respelled;
* and each remaining respelling gets a one-line declaration of its own, so that it is checked
  against its own budget: `chartDetPullbackIsoCoe`, `homOfLE_homOfLE_affine_coe` and the `_eq`
  lemmas exist for no other reason.

The structural input is the associativity coherence
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` of the pullback pseudofunctor,
recast as `pullbackComp_pentagon` and its three rearrangements, together with the fact that
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is an `CategoryTheory.eqToIso`, so that each of
its own coherences is proved by substituting the equality it is indexed by. From these,
`pullbackPrism` is the statement that the two commuting squares relating the charts of
`V ≤ V' ≤ W` to their spectra paste to the square of `V ≤ W`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

open Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The coherences of `pullbackCongr`

`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso`, so each of the
identities below is proved by substituting the equality of morphisms it is indexed by.
-/

/-- Reindexing the pullback along the trivial equality is the identity. -/
private theorem pullbackCongr_rfl {A B : Scheme.{u}} (f : A ⟶ B) :
    (pullbackCongr (rfl : f = f)).hom = 𝟙 _ := by
  simp [pullbackCongr]

/-- Reindexing along an equality and along its inverse are inverse isomorphisms, read at a
single module. -/
private theorem pullbackCongr_app_symm {A B : Scheme.{u}} {f f' : A ⟶ B} (e : f = f')
    (M : B.Modules) :
    (pullbackCongr e.symm).app M = ((pullbackCongr e).app M).symm := by
  subst e; rfl

/-- Reindexing the *outer* pullback of a composite commutes with the composition isomorphism. -/
private theorem pullbackCongr_comp_left {A B C : Scheme.{u}} {f f' : A ⟶ B} (e : f = f')
    (g : B ⟶ C) (M : C.Modules) :
    (pullbackComp f g).inv.app M ≫ (pullbackCongr e).hom.app ((pullback g).obj M) =
      (pullbackCongr (show f ≫ g = f' ≫ g by rw [e])).hom.app M ≫
        (pullbackComp f' g).inv.app M := by
  subst e; simp [pullbackCongr]

/-- Reindexing the *inner* pullback of a composite commutes with the composition isomorphism. -/
private theorem pullbackCongr_comp_right {A B C : Scheme.{u}} (f : A ⟶ B) {g g' : B ⟶ C}
    (e : g = g') (M : C.Modules) :
    (pullback f).map ((pullbackCongr e).hom.app M) ≫ (pullbackComp f g').hom.app M =
      (pullbackComp f g).hom.app M ≫
        (pullbackCongr (show f ≫ g = f ≫ g' by rw [e])).hom.app M := by
  subst e; simp [pullbackCongr]

/-! ### The pentagon of `pullbackComp` -/

/-- **The associativity coherence of the pullback pseudofunctor at a single module.** This is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` with the whiskerings and the
associator evaluated at `M`, and with its `CategoryTheory.eqToHom` named as a reindexing. -/
private theorem pullbackComp_pentagon {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (k : C ⟶ D)
    (M : D.Modules) :
    (pullback f).map ((pullbackComp g k).inv.app M) ≫
        (pullbackComp f g).hom.app ((pullback k).obj M) ≫
        (pullbackComp (f ≫ g) k).hom.app M =
      (pullbackComp f (g ≫ k)).hom.app M ≫
        (pullbackCongr (Category.assoc f g k).symm).hom.app M := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g k) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at key
  simp only [pullbackCongr, eqToIso.hom]
  rw [← key]
  simp

/-- The pentagon with the inner composition isomorphism moved to the other side. -/
private theorem pullbackComp_pentagon_hom {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : C ⟶ D) (M : D.Modules) :
    (pullbackComp f g).hom.app ((pullback k).obj M) ≫ (pullbackComp (f ≫ g) k).hom.app M =
      (pullback f).map ((pullbackComp g k).hom.app M) ≫
        (pullbackComp f (g ≫ k)).hom.app M ≫
          (pullbackCongr (Category.assoc f g k).symm).hom.app M := by
  rw [← pullbackComp_pentagon f g k M, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The pentagon with the outer composition isomorphism along `f ≫ g` moved to the other side. -/
private theorem pullbackComp_pentagon_inv {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : C ⟶ D) (M : D.Modules) :
    (pullback f).map ((pullbackComp g k).inv.app M) ≫
        (pullbackComp f g).hom.app ((pullback k).obj M) =
      (pullbackComp f (g ≫ k)).hom.app M ≫
        (pullbackCongr (Category.assoc f g k).symm).hom.app M ≫
          (pullbackComp (f ≫ g) k).inv.app M := by
  rw [← Category.assoc, ← pullbackComp_pentagon f g k M]
  simp

/-- The pentagon as an identity of isomorphisms, which is how its inverse is read off. -/
private theorem pullbackComp_pentagonIso {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : C ⟶ D) (M : D.Modules) :
    (pullbackComp f g).app ((pullback k).obj M) ≪≫ (pullbackComp (f ≫ g) k).app M =
      (pullback f).mapIso ((pullbackComp g k).app M) ≪≫
        (pullbackComp f (g ≫ k)).app M ≪≫
          (pullbackCongr (Category.assoc f g k).symm).app M :=
  Iso.ext (by simpa using pullbackComp_pentagon_hom f g k M)

/-- The pentagon read on the inverses, which is the form in which an iterated pullback is
collapsed from the inside out. -/
private theorem pullbackComp_pentagon_inv_comp {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : C ⟶ D) (M : D.Modules) :
    (pullbackComp (f ≫ g) k).inv.app M ≫
        (pullbackComp f g).inv.app ((pullback k).obj M) ≫
          (pullback f).map ((pullbackComp g k).hom.app M) =
      (pullbackCongr (Category.assoc f g k)).hom.app M ≫
        (pullbackComp f (g ≫ k)).inv.app M := by
  have h := congrArg Iso.inv (pullbackComp_pentagonIso f g k M)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at h
  rw [← Category.assoc, h]
  simp [pullbackCongr]

/-! ### The prism -/

/-- **Two commuting squares paste.** For a diagram of schemes
```
V --a--> V' --b--> W
|sV      |sV'      |sW
SV --ρ-> SV' --σ-> SW
```
with `a ≫ b = c`, `ρ ≫ σ = τ` and the three squares commuting, the comparison of the pullback
along `V ⟶ W ⟶ SW` with the pullback along `V ⟶ SV ⟶ SW` obtained by pasting the two small
squares is the one attached to the big square. -/
private theorem pullbackPrism {V V' W SV SV' SW : Scheme.{u}}
    (a : V ⟶ V') (b : V' ⟶ W) (c : V ⟶ W)
    (rho : SV ⟶ SV') (sig : SV' ⟶ SW) (tau : SV ⟶ SW)
    (sV : V ⟶ SV) (sV' : V' ⟶ SV') (sW : W ⟶ SW)
    (hab : a ≫ b = c) (hrs : rho ≫ sig = tau)
    (eh : sV ≫ rho = a ≫ sV') (eh' : sV' ≫ sig = b ≫ sW) (ec : sV ≫ tau = c ≫ sW)
    (M : SW.Modules) :
    (pullback a).map ((pullbackComp b sW).hom.app M) ≫
        (pullback a).map ((pullbackCongr eh'.symm).hom.app M) ≫
        (pullback a).map ((pullbackComp sV' sig).inv.app M) ≫
        (pullbackComp a sV').hom.app ((pullback sig).obj M) ≫
        (pullbackCongr eh.symm).hom.app ((pullback sig).obj M) ≫
        (pullbackComp sV rho).inv.app ((pullback sig).obj M) ≫
        (pullback sV).map ((pullbackComp rho sig).hom.app M) ≫
        (pullback sV).map ((pullbackCongr hrs).hom.app M) =
      (pullbackComp a b).hom.app ((pullback sW).obj M) ≫
        (pullbackCongr hab).hom.app ((pullback sW).obj M) ≫
        (pullbackComp c sW).hom.app M ≫ (pullbackCongr ec.symm).hom.app M ≫
        (pullbackComp sV tau).inv.app M := by
  subst hab
  subst hrs
  simp only [pullbackCongr_rfl, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  rw [reassoc_of% pullbackComp_pentagon_hom a b sW M,
    reassoc_of% pullbackComp_pentagon_inv a sV' sig M,
    reassoc_of% pullbackCongr_comp_right a eh'.symm M,
    reassoc_of% pullbackCongr_comp_left eh.symm sig M,
    pullbackComp_pentagon_inv_comp sV rho sig M]
  simp [pullbackCongr]

/-- **The cocycle condition for a chart comparison transported along two commuting squares.**
With the diagram of `pullbackPrism`, modules `M` on `SW`, `M'` on `SV'` and `MV` on `SV`, and
comparisons `Psi'`, `Psi`, `Omega` on the spectra satisfying the cocycle condition `hspec`
against the pasting `Cmp`, the three transported comparisons `Fh`, `Fh'`, `Fc` satisfy the
cocycle condition on the open subschemes.

Each of `Cmp`, `Fh`, `Fh'`, `Fc` is a variable whose definition is named by an
isomorphism-valued hypothesis, and the reindexing `pcg` is a variable too; see the implementation
notes. -/
private theorem pullbackTransChase {V V' W SV SV' SW : Scheme.{u}}
    (a : V ⟶ V') (b : V' ⟶ W) (c : V ⟶ W)
    (rho : SV ⟶ SV') (sig : SV' ⟶ SW) (tau : SV ⟶ SW)
    (sV : V ⟶ SV) (sV' : V' ⟶ SV') (sW : W ⟶ SW)
    (hab : a ≫ b = c) (hrs : rho ≫ sig = tau)
    (eh : sV ≫ rho = a ≫ sV') (eh' : sV' ≫ sig = b ≫ sW) (ec : sV ≫ tau = c ≫ sW)
    {M : SW.Modules} {M' : SV'.Modules} {MV : SV.Modules}
    (Psi' : (pullback sig).obj M ≅ M') (Psi : (pullback rho).obj M' ≅ MV)
    (Omega : (pullback tau).obj M ≅ MV)
    {Cmp : (pullback rho).obj ((pullback sig).obj M) ≅ (pullback tau).obj M}
    {Fh : (pullback a).obj ((pullback sV').obj M') ≅ (pullback sV).obj MV}
    {Fh' : (pullback b).obj ((pullback sW).obj M) ≅ (pullback sV').obj M'}
    {Fc : (pullback c).obj ((pullback sW).obj M) ≅ (pullback sV).obj MV}
    (hCmp : Cmp = (pullbackComp rho sig).app M ≪≫ (pullbackCongr hrs).app M)
    (hFh : Fh = (pullbackComp a sV').app M' ≪≫ (pullbackCongr eh.symm).app M' ≪≫
      ((pullbackComp sV rho).app M').symm ≪≫ (pullback sV).mapIso Psi)
    (hFh' : Fh' = (pullbackComp b sW).app M ≪≫ (pullbackCongr eh'.symm).app M ≪≫
      ((pullbackComp sV' sig).app M).symm ≪≫ (pullback sV').mapIso Psi')
    (hFc : Fc = (pullbackComp c sW).app M ≪≫ (pullbackCongr ec.symm).app M ≪≫
      ((pullbackComp sV tau).app M).symm ≪≫ (pullback sV).mapIso Omega)
    (pcg : pullback (a ≫ b) ⟶ pullback c) (hpcg : pcg = (pullbackCongr hab).hom)
    (hspec : (pullback rho).map Psi'.hom ≫ Psi.hom = Cmp.hom ≫ Omega.hom) :
    (pullback a).map Fh'.hom ≫ Fh.hom =
      (pullbackComp a b).hom.app ((pullback sW).obj M) ≫
        pcg.app ((pullback sW).obj M) ≫ Fc.hom := by
  subst hpcg
  subst hCmp
  subst hFh
  subst hFh'
  subst hFc
  have hcomb : (pullback sV).map ((pullback rho).map Psi'.hom) ≫ (pullback sV).map Psi.hom =
      (pullback sV).map ((pullbackComp rho sig).hom.app M) ≫
        (pullback sV).map ((pullbackCongr hrs).hom.app M) ≫ (pullback sV).map Omega.hom := by
    rw [← Functor.map_comp, hspec]
    simp [Functor.map_comp]
  have n1 := (pullbackComp a sV').hom.naturality Psi'.hom
  have n2 := (pullbackCongr eh.symm).hom.naturality Psi'.hom
  have n3 := (pullbackComp sV rho).inv.naturality Psi'.hom
  dsimp only [Functor.comp_map] at n1 n3
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% n3, hcomb,
    reassoc_of% pullbackPrism a b c rho sig tau sV sV' sW hab hrs eh eh' ec M]

/-! ### The restriction form is the pullback form -/

/-- A five-fold composite of isomorphisms is the inverse of the reversed composite of the first
four, followed by the fifth. The inverse of the middle factor is a variable paired with its
definition, so that the concrete isomorphism of a chart comparison can be supplied. -/
private theorem isoFiveChase {D : Type*} [Category D] {P Q R S T U : D}
    (A : P ≅ Q) (B : Q ≅ R) (Cc : R ≅ S) (E : S ≅ T) (F : T ≅ U)
    (C' : S ≅ R) (hC : C' = Cc.symm) :
    A ≪≫ B ≪≫ Cc ≪≫ E ≪≫ F = (E.symm ≪≫ C' ≪≫ B.symm ≪≫ A.symm).symm ≪≫ F := by
  subst hC
  simp [Iso.trans_assoc]

/-- **The restriction form of the chart comparison is the pullback form.** For affine opens
`V ≤ W` of `X`, the identification of the determinant of `L` on `V` with the restriction along
`V ⟶ W` of the determinant on `W` is the inverse of
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso`, followed by the identification of the
pullback along `V ⟶ W` with the restriction along `V ⟶ W`.

Both sides are the same five factors, up to the associativity of `CategoryTheory.Iso.trans`, up to
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` being an `CategoryTheory.eqToIso` and so
self-inverse along `Eq.symm`, and up to `CategoryTheory.Iso.symm_symm`. -/
theorem chartDetRestrictIso_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    chartDetRestrictIso L h =
      (chartDetPullbackIso L h).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback
          (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app (chartDet L W)).symm :=
  isoFiveChase
    ((Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h).symm)
    ((Scheme.Modules.pullbackComp V.2.isoSpec.hom (Spec.map (affineRestriction X h))).app
      (chartDetSpec L W))
    ((Scheme.Modules.pullbackCongr (isoSpec_hom_specMap_chartRestriction h)).app
      (chartDetSpec L W))
    (((Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h)) W.2.isoSpec.hom).app
      (chartDetSpec L W)).symm)
    (((Scheme.Modules.restrictFunctorIsoPullback (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app
      (chartDet L W)).symm)
    ((Scheme.Modules.pullbackCongr (isoSpec_hom_specMap_chartRestriction h).symm).app
      (chartDetSpec L W))
    (pullbackCongr_app_symm (isoSpec_hom_specMap_chartRestriction h) (chartDetSpec L W))

/-- **The restriction form of the chart comparison is the pullback form**, on the underlying
morphisms. This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_eq` read on `hom`. -/
theorem chartDetRestrictIso_hom (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    (chartDetRestrictIso L h).hom =
      (chartDetPullbackIso L h).inv ≫
        ((Scheme.Modules.restrictFunctorIsoPullback
          (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app (chartDet L W)).inv := by
  rw [chartDetRestrictIso_eq]
  rfl

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso` with the inclusion spelled through
`AlgebraicGeometry.AffineOpensGlue.coe_le_coe`. The two spellings are two names for one proof;
naming the respelt isomorphism keeps its defeq check out of the chases below. -/
private def chartDetPullbackIsoCoe (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    (Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe h))).obj (chartDet L W) ≅
      chartDet L V :=
  chartDetPullbackIso L h

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_hom` with the inclusion spelled
through `AlgebraicGeometry.AffineOpensGlue.coe_le_coe`. -/
private theorem chartDetRestrictIso_hom_coe (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) :
    (chartDetRestrictIso L h).hom =
      (chartDetPullbackIsoCoe L h).inv ≫
        ((Scheme.Modules.restrictFunctorIsoPullback
          (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app (chartDet L W)).inv :=
  chartDetRestrictIso_hom L h

/-! ### The pullback form composes -/

/-- The definition of `AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso`, named as an
equality of isomorphisms so that a chase can consume it without unfolding the definition
underneath `CategoryTheory.Iso.hom`, and with its inclusion respelt through
`AlgebraicGeometry.AffineOpensGlue.coe_le_coe`. -/
private theorem chartDetPullbackIso_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    chartDetPullbackIso L h =
      (Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
            W.2.isoSpec.hom).app (chartDetSpec L W) ≪≫
        (Scheme.Modules.pullbackCongr (isoSpec_hom_specMap_chartRestriction h).symm).app
          (chartDetSpec L W) ≪≫
        ((Scheme.Modules.pullbackComp V.2.isoSpec.hom (Spec.map (affineRestriction X h))).app
          (chartDetSpec L W)).symm ≪≫
        (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h) :=
  rfl

/-- The definition of
`AlgebraicGeometry.DeterminantTwoTerm.chartSpecPullbackCompIso`, with its factorisation of
`Spec ρ_{V,W}` presented as a hypothesis rather than as the proof the definition uses. Named so
that the one proof-irrelevance step it needs is checked here and not inside a larger chase. -/
private theorem chartSpecPullbackCompIso_eq {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W)
    (hrs : Spec.map (affineRestriction X h) ≫ Spec.map (affineRestriction X h') =
      Spec.map (affineRestriction X (h.trans h')))
    (M : (Spec Γ(X, (W.1 : X.Opens))).Modules) :
    chartSpecPullbackCompIso h h' M =
      (Scheme.Modules.pullbackComp (Spec.map (affineRestriction X h))
          (Spec.map (affineRestriction X h'))).app M ≪≫
        (Scheme.Modules.pullbackCongr hrs).app M :=
  rfl

/-- **The pullback form of the chart comparison composes along a chain of two inclusions.** For
affine opens `V ≤ V' ≤ W` of `X` and a factorisation `hfg` of the inclusion `V ⟶ W` through `V'`,
the pullback to `V` of the comparison of `V' ≤ W` followed by the comparison of `V ≤ V'` is the
comparison of `V ≤ W`, read through `AlgebraicGeometry.Scheme.Modules.pullbackComp` and the
reindexing along `hfg`.

The hypothesis `hspec` is the same cocycle condition on the spectra; the two are related by the
pasting `pullbackPrism` of the two commuting squares
`AlgebraicGeometry.DeterminantTwoTerm.isoSpec_hom_specMap_chartRestriction`. The reindexing
enters as a variable `pcg` named by `hpcg`, so that the module it is evaluated at can be
respelled; see the implementation notes. -/
theorem chartDetPullbackIso_trans (L : PerfectTwoTermAmplitude X)
    {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W)
    (hfg : X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫
        X.homOfLE (AffineOpensGlue.coe_le_coe h') =
      X.homOfLE (AffineOpensGlue.coe_le_coe (h.trans h')))
    (pcg : Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫
        X.homOfLE (AffineOpensGlue.coe_le_coe h')) ⟶
      Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe (h.trans h'))))
    (hpcg : pcg = (Scheme.Modules.pullbackCongr hfg).hom)
    (hspec : (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecPullbackIso L h').hom ≫ (chartDetSpecPullbackIso L h).hom =
        (chartSpecPullbackCompIso h h' (chartDetSpec L W)).hom ≫
          (chartDetSpecPullbackIso L (h.trans h')).hom) :
    (Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
          (chartDetPullbackIso L h').hom ≫ (chartDetPullbackIso L h).hom =
      (Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
            (X.homOfLE (AffineOpensGlue.coe_le_coe h'))).hom.app (chartDet L W) ≫
        pcg.app (chartDet L W) ≫ (chartDetPullbackIso L (h.trans h')).hom := by
  have hrs : Spec.map (affineRestriction X h) ≫ Spec.map (affineRestriction X h') =
      Spec.map (affineRestriction X (h.trans h')) :=
    specMap_chartRestriction_comp (AffineOpensGlue.coe_le_coe h) (AffineOpensGlue.coe_le_coe h')
  exact pullbackTransChase (X.homOfLE (AffineOpensGlue.coe_le_coe h))
    (X.homOfLE (AffineOpensGlue.coe_le_coe h'))
    (X.homOfLE (AffineOpensGlue.coe_le_coe (h.trans h')))
    (Spec.map (affineRestriction X h)) (Spec.map (affineRestriction X h'))
    (Spec.map (affineRestriction X (h.trans h')))
    V.2.isoSpec.hom V'.2.isoSpec.hom W.2.isoSpec.hom hfg hrs
    (isoSpec_hom_specMap_chartRestriction h) (isoSpec_hom_specMap_chartRestriction h')
    (isoSpec_hom_specMap_chartRestriction (h.trans h'))
    (chartDetSpecPullbackIso L h') (chartDetSpecPullbackIso L h)
    (chartDetSpecPullbackIso L (h.trans h'))
    (chartSpecPullbackCompIso_eq h h' hrs (chartDetSpec L W)) (chartDetPullbackIso_eq L h)
    (chartDetPullbackIso_eq L h') (chartDetPullbackIso_eq L (h.trans h')) pcg hpcg hspec

/-! ### The restriction form composes -/

/-- **The cocycle condition passes from the pullback functors to the restriction functors.** For
open immersions `f`, `g` and a factorisation `f ≫ g = k`, comparisons `Fh`, `Fh'`, `Fc` of
pullbacks satisfying the cocycle condition `hcoc` give, after transport along
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, the cocycle condition for the
restriction functors against the collapsing isomorphism `T`.

The transport is `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq`
and the naturality of `restrictFunctorIsoPullback`. The variables `T` and `pcg` with their
hypotheses `hT` and `hpcg` keep
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` and the reindexing out of the chase;
see the implementation notes. -/
private theorem restrictChase {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k] (hfg : f ≫ g = k)
    (N : C.Modules) {MB : B.Modules} {MA : A.Modules}
    (Fh : (pullback f).obj MB ≅ MA) (Fh' : (pullback g).obj N ≅ MB)
    (Fc : (pullback k).obj N ≅ MA)
    (T : restrictFunctor g ⋙ restrictFunctor f ≅ restrictFunctor k)
    (pcg : pullback (f ≫ g) ⟶ pullback k)
    (hT : T = (restrictFunctorComp f g).symm ≪≫ restrictFunctorCongr hfg)
    (hpcg : pcg = (pullbackCongr hfg).hom)
    (hcoc : (pullback f).map Fh'.hom ≫ Fh.hom =
      (pullbackComp f g).hom.app N ≫ pcg.app N ≫ Fc.hom) :
    (Fh.inv ≫ ((restrictFunctorIsoPullback f).app MB).inv) ≫
        (restrictFunctor f).map (Fh'.inv ≫ ((restrictFunctorIsoPullback g).app N).inv) ≫
        T.hom.app N =
      Fc.inv ≫ ((restrictFunctorIsoPullback k).app N).inv := by
  subst hT
  subst hpcg
  have hiso : (pullback f).mapIso Fh' ≪≫ Fh =
      (pullbackComp f g).app N ≪≫ (pullbackCongr hfg).app N ≪≫ Fc :=
    Iso.ext (by simpa using hcoc)
  have hinv := congrArg Iso.inv hiso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at hinv
  have hcoh := NatTrans.congr_app
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq f g hfg) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hcoh
  have hnat := (restrictFunctorIsoPullback f).inv.naturality Fh'.inv
  have hcancel : (restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app N) ≫
      (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [Iso.eq_comp_inv]
  simp only [Iso.app_hom, Iso.app_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [hcoh, reassoc_of% hcancel, ← reassoc_of% hnat, reassoc_of% hinv]
  simp

/-- The inclusions of the underlying opens attached to affine opens `V ≤ V' ≤ W` of `X`
compose. This is `AlgebraicGeometry.Scheme.homOfLE_homOfLE` with its conclusion spelled through
`AlgebraicGeometry.AffineOpensGlue.coe_le_coe`. -/
private theorem homOfLE_homOfLE_affine_coe {V V' W : X.affineOpens} (h : V ≤ V')
    (h' : V' ≤ W) :
    X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ X.homOfLE (AffineOpensGlue.coe_le_coe h') =
      X.homOfLE (AffineOpensGlue.coe_le_coe (h.trans h')) :=
  X.homOfLE_homOfLE _ _

/-- The definition of `AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso`, named as an
equality of isomorphisms. -/
private theorem restrictFunctorTransIso_eq {V V' W : X.affineOpens} (h : V ≤ V')
    (h' : V' ≤ W) :
    AffineOpensGlue.restrictFunctorTransIso (AffineOpensGlue.coe_le_coe h)
        (AffineOpensGlue.coe_le_coe h') (AffineOpensGlue.coe_le_coe (h.trans h')) =
      (Scheme.Modules.restrictFunctorComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
          (X.homOfLE (AffineOpensGlue.coe_le_coe h'))).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (homOfLE_homOfLE_affine_coe h h') :=
  rfl

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso_trans` with the chart comparisons
replaced by the respelt `chartDetPullbackIsoCoe`, which is what `restrictChase` is fed. -/
private theorem chartDetPullbackIso_trans_coe (L : PerfectTwoTermAmplitude X)
    {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W)
    (hspec : (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecPullbackIso L h').hom ≫ (chartDetSpecPullbackIso L h).hom =
        (chartSpecPullbackCompIso h h' (chartDetSpec L W)).hom ≫
          (chartDetSpecPullbackIso L (h.trans h')).hom) :
    (Scheme.Modules.pullback (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
          (chartDetPullbackIsoCoe L h').hom ≫ (chartDetPullbackIsoCoe L h).hom =
      (Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
            (X.homOfLE (AffineOpensGlue.coe_le_coe h'))).hom.app (chartDet L W) ≫
        (Scheme.Modules.pullbackCongr (homOfLE_homOfLE_affine_coe h h')).hom.app
          (chartDet L W) ≫ (chartDetPullbackIsoCoe L (h.trans h')).hom :=
  chartDetPullbackIso_trans L h h' (homOfLE_homOfLE_affine_coe h h')
    (Scheme.Modules.pullbackCongr (homOfLE_homOfLE_affine_coe h h')).hom rfl hspec

/-- **The chart comparison of the determinant on the open subschemes is transitive.** For affine
opens `V ≤ V' ≤ W` of `X`, the comparison of `V ≤ V'` followed by the restriction to `V` of the
comparison of `V' ≤ W` is the comparison of `V ≤ W`, read through the collapsing isomorphism
`AlgebraicGeometry.AffineOpensGlue.restrictFunctorTransIso` of the two restriction functors.

This is the hypothesis of `AlgebraicGeometry.AffineOpensGlue.ofRestrictIso` at the family
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`, so with the cocycle condition `hspec`
on the spectra it assembles the determinants of `L` on the charts into a glueing datum. The proof
turns the whole identity into one about `AlgebraicGeometry.Scheme.Modules.pullback` by
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_hom`, where it is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPullbackIso_trans`. -/
theorem chartDetRestrictIso_trans (L : PerfectTwoTermAmplitude X) {V V' W : X.affineOpens}
    (h : V ≤ V') (h' : V' ≤ W)
    (hspec : (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecPullbackIso L h').hom ≫ (chartDetSpecPullbackIso L h).hom =
        (chartSpecPullbackCompIso h h' (chartDetSpec L W)).hom ≫
          (chartDetSpecPullbackIso L (h.trans h')).hom) :
    (chartDetRestrictIso L h).hom ≫
        (Scheme.Modules.restrictFunctor
            (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map (chartDetRestrictIso L h').hom ≫
        (AffineOpensGlue.restrictFunctorTransIso (AffineOpensGlue.coe_le_coe h)
            (AffineOpensGlue.coe_le_coe h')
            (AffineOpensGlue.coe_le_coe (h.trans h'))).hom.app (chartDet L W) =
      (chartDetRestrictIso L (h.trans h')).hom := by
  rw [chartDetRestrictIso_hom_coe, chartDetRestrictIso_hom_coe, chartDetRestrictIso_hom_coe]
  exact restrictChase (X.homOfLE (AffineOpensGlue.coe_le_coe h))
    (X.homOfLE (AffineOpensGlue.coe_le_coe h'))
    (X.homOfLE (AffineOpensGlue.coe_le_coe (h.trans h'))) (homOfLE_homOfLE_affine_coe h h')
    (chartDet L W) (chartDetPullbackIsoCoe L h) (chartDetPullbackIsoCoe L h')
    (chartDetPullbackIsoCoe L (h.trans h'))
    (AffineOpensGlue.restrictFunctorTransIso (AffineOpensGlue.coe_le_coe h)
      (AffineOpensGlue.coe_le_coe h') (AffineOpensGlue.coe_le_coe (h.trans h')))
    (Scheme.Modules.pullbackCongr (homOfLE_homOfLE_affine_coe h h')).hom
    (restrictFunctorTransIso_eq h h') rfl (chartDetPullbackIso_trans_coe L h h' hspec)

end AlgebraicGeometry.DeterminantTwoTerm

end
