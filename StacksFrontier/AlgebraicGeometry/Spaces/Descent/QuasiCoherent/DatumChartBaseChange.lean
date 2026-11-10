module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumChartLaws
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin

/-!
# The identity law and the change of test space of a descent datum's transition on a chart

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces over `X`, and let `D` be a descent datum for quasi-coherent modules relative to that
family.  On a test space `T` carrying a morphism `v` to `Y i ×_X Y j` and the two étale
composites `vi`, `vj` to the members, the transition of `D` is read on the sections over a chart
`U` of `T` as a bijection

`D.F i` over the chart `U ≫ vi` of `Y i`  ⟷  `D.F j` over the chart `U ≫ vj` of `Y j`,

namely `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`.
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean` supplies the two
laws that make that reading natural in the chart and compositional across three members.  This
file supplies the two remaining ones: the reading from a member **to itself** is the identity,
and the reading is natural in the **test space**.

The two together are what an assembly of the readings into a presheaf on the charts of the
members of a covering needs.  Such a presheaf has to read the transition attached to a morphism
of member charts on a test space built from the *source* of that morphism, so a composite of two
such morphisms presents its first factor on the wrong test space; the law below is what moves it.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_refl` and `.transitionSect_id`:
  **the transition from a member to itself is the identity.**  The cocycle condition at the
  triple `i, i, i` says that the transition read on a test space carrying a single morphism to
  `Y i` is idempotent, and it is an isomorphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_base`,
  `.transitionHom_base_apply` and `.transitionSect_base`: **the reading is natural in the test
  space.**  Along a morphism `w : T' ⟶ T` of test spaces the reading over a chart `U` of `T'` is
  the reading over `T` taken over the chart of `T` that `U` induces.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_compIso_inv_etaleSectInv`: reading a
  section of an étale restriction along a composite back as a section of the iterated inverse
  image is reading it back along the second factor over the induced chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` bundles the reading as a
  **morphism of the étale restrictions** of the two component modules to the test space, and
  `.transitionEtaleForm_id`, `.transitionEtaleForm_comp` are the identity law and the cocycle for
  it.  Naturality in the chart needs no law in this form: it is naturality of a morphism of
  sheaves of modules.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.hom_val_app_refl_congr`,
  `.hom_val_app_trans₃_congr`, `.hom_eq_id_of_refl`, `.inv_comp_comp_hom_eq_id`,
  `.hom_comp_congr`, `.etaleForm_comp_congr`, `.val_app_trans₃_apply` and
  `.etaleModulePullback_map_val_app_apply`: the readings of composites and of components of
  isomorphisms that the proofs cross, every one of them stated on variables.

## Implementation notes

**Both laws are stated with the reading written out**, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean`: a statement in
which `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` has to be matched against the
written-out composite exhausts the elaborator's recursion depth, so no statement may mix the two
spellings.  The generic lemmas on variables are what lets each written-out statement be reached
in one definitional step: `.hom_val_app_trans₃_congr` carries each of the four morphisms as a
variable identified with a component by a hypothesis, so the conclusion is spelled the way the
consumer needs it rather than the way the isomorphisms are built.

Unlike the two laws of `DatumChartLaws`, the change of test space does need the compatibility
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` of the
comparison of Stacks 03LU with étale restriction — two different inverse images of one module are
compared — and it is discharged by
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`, so everything below is
unconditional.  The associativity coherence of the same comparison enters through
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_comp`, which is itself unconditional.

The two charts of `Y j` that the change of test space compares, `U ≫ (w ≫ vj)` and
`(U ≫ w) ≫ vj`, are the same chart on the nose by
`AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp_obj_comp`, so the two sides of
the law are sections over literally one chart and no transport appears.

**Why the change of test space has no morphism-level form.**  The bundled reading
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionEtaleForm` carries the identity law and
the cocycle as equations of morphisms, which is what makes them cheap; the change of test space
would be
`(etaleModulePullback w hw).map (transitionEtaleForm … v …) = transitionEtaleForm … (w ≫ v) …`,
and that **statement** — not its proof — exhausts the heartbeat budget at `whnf`.  What it asks
of the elaborator is to see the source of the left side,
`(etaleModulePullback w).obj ((etaleModulePullback vi).obj (D.F i))`, as the source of the right
side, `(etaleModulePullback (w ≫ vi)).obj (D.F i)`, inside the type of a morphism of modules.
The two modules are equal by `Eq.refl`, and *that* equation elaborates in milliseconds; it is
asking for the identification in the endpoints of a hom that does not terminate.  So the change
of test space is available only on sections, which is the form
`.transitionSect_base` has, and a consumer assembling the presheaf has to descend to sections for
`map_comp` even though the identity law and the cocycle are available above them.

Two further measurements, both of statements that must therefore never be written.  Reading
`transitionEtaleForm` on a section and matching it against the written-out composite —
`(transitionEtaleForm …).val.app (.op U) s = etaleSect … ((transitionHom …).val.app (.op U)
(etaleSectInv … s))` — exhausts the recursion depth, as does the same statement for the
composite taken in the category of modules of sections rather than in the category of sheaves of
modules.  Each of the three definitional steps that statement crosses is free on its own:
`etaleSect … m = ((modulePullbackIsoEtaleModulePullback …).hom.app M).val.app (.op U) m` is `rfl`
in milliseconds, so is `.etaleModulePullback_map_val_app_apply`, and so is
`.val_app_trans₃_apply` with its four morphisms as variables.  It is only the composite match
that is fatal, which is why the three are recorded separately above: a consumer crosses them one
at a time with `Eq.trans`, and never names two spellings in one statement.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- A morphism of modules which is the component of an isomorphism equal to the identity acts as
the identity on a section.  Stated on variables. -/
theorem hom_val_app_refl_congr {D₀ : AlgebraicSpaces B S hS}
    {P : Modules.{u, u} B S hS D₀.1 D₀.2} {e : P ≅ P} (h : e = Iso.refl P) (ψ : P ⟶ P)
    (hψ : ψ = e.hom) (U : SmallEtale B S hS D₀.1) (m : P.val.obj (.op U)) :
    ψ.val.app (.op U) m = m := by
  rw [hψ, h]
  rfl

/-- **The transition of a descent datum from a member to itself is the identity.**  The cocycle
condition at the triple `i, i, i` on a test space carrying one morphism to `Y i` says that the
transition read there is idempotent; being an isomorphism, it is the identity. -/
theorem transitionOn_refl (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i : I)
    (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w) :
    transitionOn B S hS Yi f D.F D.transition i i v w w hi hj = Iso.refl _ := by
  have h := congrArg Iso.hom (D.cocycle i i i T w w w v v v hi hj hi hj hi hj)
  refine Iso.ext ((Iso.cancel_iso_hom_right _ _
    (transitionOn B S hS Yi f D.F D.transition i i v w w hi hj)).1 ?_)
  simpa using h

/-- The transition of a descent datum from a member to itself, read as a bare morphism, acts as
the identity on a section. -/
theorem transitionHom_id_apply (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i : I)
    (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1)
    (m : ((modulePullback B S hS w).obj (D.F i)).val.obj (.op U)) :
    (transitionHom B S hS Yi f D i i v w w hi hj).val.app (.op U) m = m :=
  hom_val_app_refl_congr B S hS (transitionOn_refl B S hS Yi f D i v w hi hj)
    (transitionHom B S hS Yi f D i i v w w hi hj) rfl U m

/-- **The transition of a descent datum from a member to itself, read on sections over a chart,
is the identity.**  This is the third of the laws that make
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` presheaf data: the reading is
written out, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean`. -/
theorem transitionSect_id (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i : I)
    (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i) (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS w hw).obj U))) :
    etaleSect B S hS w hw (D.F i) U
        ((transitionHom B S hS Yi f D i i v w w hi hj).val.app (.op U)
          (etaleSectInv B S hS w hw (D.F i) U s)) = s :=
  (congrArg (etaleSect B S hS w hw (D.F i) U)
      (transitionHom_id_apply B S hS Yi f D i v w hi hj U
        (etaleSectInv B S hS w hw (D.F i) U s))).trans
    (etaleSect_etaleSectInv B S hS w hw (D.F i) U s)

/-! ### Change of test space -/

/-- Three morphisms of modules which are the components of three isomorphisms composing to a
fourth agree, on a section, with the component of that fourth.  The four morphisms are variables
identified with the four components by hypotheses, which is what lets a consumer state the
conclusion in its own spelling of each of them. -/
theorem hom_val_app_trans₃_congr {D₀ : AlgebraicSpaces B S hS}
    {P Q R W : Modules.{u, u} B S hS D₀.1 D₀.2} {e₁ : P ≅ Q} {e₂ : Q ≅ R} {e₃ : R ≅ W}
    {E : P ≅ W} (h : e₁ ≪≫ e₂ ≪≫ e₃ = E) (ψ₁ : P ⟶ Q) (ψ₂ : Q ⟶ R) (ψ₃ : R ⟶ W) (ψ : P ⟶ W)
    (hψ₁ : ψ₁ = e₁.hom) (hψ₂ : ψ₂ = e₂.hom) (hψ₃ : ψ₃ = e₃.hom) (hψ : ψ = E.hom)
    (U : SmallEtale B S hS D₀.1) (m : P.val.obj (.op U)) :
    ψ.val.app (.op U) m = ψ₃.val.app (.op U) (ψ₂.val.app (.op U) (ψ₁.val.app (.op U) m)) := by
  subst hψ₁ hψ₂ hψ₃ hψ
  rw [← h]
  rfl

/-- **A pairwise isomorphism of a descent datum read on a test space pulled back along a
morphism into it.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_comp` solved for the reading on the
source of the morphism. -/
theorem transitionOn_base (D : DescentDatum B S hS Yi f) {T T' : AlgebraicSpaces B S hS}
    (w : T' ⟶ T) (i j : I) (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (w ≫ v) ≫ pairFst B S hS Yi f i j = w ≫ vi)
    (hj' : (w ≫ v) ≫ pairSnd B S hS Yi f i j = w ≫ vj) :
    ((modulePullbackCompIso B S hS w vi).app (D.F i)).symm ≪≫
        (modulePullback B S hS w).mapIso
          (transitionOn B S hS Yi f D.F D.transition i j v vi vj hi hj) ≪≫
        (modulePullbackCompIso B S hS w vj).app (D.F j) =
      transitionOn B S hS Yi f D.F D.transition i j (w ≫ v) (w ≫ vi) (w ≫ vj) hi' hj' := by
  rw [transitionOn_comp B S hS Yi f D.F D.transition w i j v vi vj hi hj]
  simp

/-- **The transition of a descent datum read on a test space, pulled back along a morphism into
that space, read on a chart of the source.**  The transition over the source is the transition
over the target read over the induced chart, once the section of the inverse image is carried
across the comparison of Stacks 03LU. -/
theorem transitionHom_base_apply (D : DescentDatum B S hS Yi f)
    {T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (hw : IsEtale B S hS w.hom) (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvj : IsEtale B S hS vj.hom) (hwvj : IsEtale B S hS (w ≫ vj).hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (w ≫ v) ≫ pairFst B S hS Yi f i j = w ≫ vi)
    (hj' : (w ≫ v) ≫ pairSnd B S hS Yi f i j = w ≫ vj)
    (U : SmallEtale B S hS T'.1)
    (m : ((modulePullback B S hS (w ≫ vi)).obj (D.F i)).val.obj (.op U)) :
    etaleSect B S hS (w ≫ vj) hwvj (D.F j) U
        ((transitionHom B S hS Yi f D i j (w ≫ v) (w ≫ vi) (w ≫ vj) hi' hj').val.app
          (.op U) m) =
      etaleSect B S hS vj hvj (D.F j) ((smallEtalePostcomp B S hS w hw).obj U)
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app
          (.op ((smallEtalePostcomp B S hS w hw).obj U))
          (etaleSect B S hS w hw ((modulePullback B S hS vi).obj (D.F i)) U
            (((modulePullbackCompIso B S hS w vi).inv.app (D.F i)).val.app (.op U) m))) :=
  ((congrArg (etaleSect B S hS (w ≫ vj) hwvj (D.F j) U)
        (hom_val_app_trans₃_congr B S hS
          (transitionOn_base B S hS Yi f D w i j v vi vj hi hj hi' hj')
          ((modulePullbackCompIso B S hS w vi).inv.app (D.F i))
          ((modulePullback B S hS w).map
            (transitionHom B S hS Yi f D i j v vi vj hi hj))
          ((modulePullbackCompIso B S hS w vj).hom.app (D.F j))
          (transitionHom B S hS Yi f D i j (w ≫ v) (w ≫ vi) (w ≫ vj) hi' hj')
          rfl rfl rfl rfl U m)).trans
      ((modulePullbackCompIsoEtaleRestriction B S hS).comp_app w vj hw hvj hwvj (D.F j) U
        (((modulePullback B S hS w).map
            (transitionHom B S hS Yi f D i j v vi vj hi hj)).val.app (.op U)
          (((modulePullbackCompIso B S hS w vi).inv.app (D.F i)).val.app (.op U) m)))).trans
    (congrArg (etaleSect B S hS vj hvj (D.F j) ((smallEtalePostcomp B S hS w hw).obj U))
      (etaleSect_map B S hS w hw (transitionHom B S hS Yi f D i j v vi vj hi hj) U
        (((modulePullbackCompIso B S hS w vi).inv.app (D.F i)).val.app (.op U) m)))

/-- Reading a section of an étale restriction along a composite back as a section of the
iterated inverse image, through the comparison of Stacks 03LU, is reading it back along the
second factor over the induced chart. -/
theorem etaleSect_compIso_inv_etaleSectInv {C₁ T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T)
    (hw : IsEtale B S hS w.hom) (vi : T ⟶ C₁) (hvi : IsEtale B S hS vi.hom)
    (hwvi : IsEtale B S hS (w ≫ vi).hom) (M : Modules.{u, u} B S hS C₁.1 C₁.2)
    (U : SmallEtale B S hS T'.1)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj
      ((smallEtalePostcomp B S hS w hw).obj U)))) :
    etaleSect B S hS w hw ((modulePullback B S hS vi).obj M) U
        (((modulePullbackCompIso B S hS w vi).inv.app M).val.app (.op U)
          (etaleSectInv B S hS (w ≫ vi) hwvi M U s)) =
      etaleSectInv B S hS vi hvi M ((smallEtalePostcomp B S hS w hw).obj U) s :=
  (etaleSectInv_etaleSect B S hS vi hvi M ((smallEtalePostcomp B S hS w hw).obj U)
        (etaleSect B S hS w hw ((modulePullback B S hS vi).obj M) U
          (((modulePullbackCompIso B S hS w vi).inv.app M).val.app (.op U)
            (etaleSectInv B S hS (w ≫ vi) hwvi M U s)))).symm.trans
    ((congrArg (etaleSectInv B S hS vi hvi M ((smallEtalePostcomp B S hS w hw).obj U))
        (((etaleSect_comp_inv B S hS w vi hw hvi hwvi
                  (ModulePullbackCompIsoEtaleRestriction.toComp B S hS
                    (AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction B S hS)
                    w vi _ _ _)
                  M U (etaleSectInv B S hS (w ≫ vi) hwvi M U s)).trans
              (etaleSect_etaleSectInv B S hS (w ≫ vi) hwvi M U s)).trans
          (etaleSect_etaleSectInv B S hS vi hvi M
            ((smallEtalePostcomp B S hS w hw).obj U) s).symm)).trans
      (etaleSectInv_etaleSect B S hS vi hvi M ((smallEtalePostcomp B S hS w hw).obj U)
        (etaleSectInv B S hS vi hvi M ((smallEtalePostcomp B S hS w hw).obj U) s)))

/-- **The transition of a descent datum, read on sections over a chart, is natural in the test
space.**  This is the fourth of the laws that make
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` presheaf data: the reading over a
chart `U` of a test space `T'` mapping to a test space `T` is the reading over `T` taken over the
chart of `T` that `U` induces.  Both sides are written out. -/
theorem transitionSect_base (D : DescentDatum B S hS Yi f) {T T' : AlgebraicSpaces B S hS}
    (w : T' ⟶ T) (hw : IsEtale B S hS w.hom) (i j : I) (v : T ⟶ pair B S hS Yi f i j)
    (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (hvi : IsEtale B S hS vi.hom)
    (hvj : IsEtale B S hS vj.hom) (hwvi : IsEtale B S hS (w ≫ vi).hom)
    (hwvj : IsEtale B S hS (w ≫ vj).hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (hi' : (w ≫ v) ≫ pairFst B S hS Yi f i j = w ≫ vi)
    (hj' : (w ≫ v) ≫ pairSnd B S hS Yi f i j = w ≫ vj)
    (U : SmallEtale B S hS T'.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj
      ((smallEtalePostcomp B S hS w hw).obj U)))) :
    etaleSect B S hS (w ≫ vj) hwvj (D.F j) U
        ((transitionHom B S hS Yi f D i j (w ≫ v) (w ≫ vi) (w ≫ vj) hi' hj').val.app (.op U)
          (etaleSectInv B S hS (w ≫ vi) hwvi (D.F i) U s)) =
      etaleSect B S hS vj hvj (D.F j) ((smallEtalePostcomp B S hS w hw).obj U)
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app
          (.op ((smallEtalePostcomp B S hS w hw).obj U))
          (etaleSectInv B S hS vi hvi (D.F i)
            ((smallEtalePostcomp B S hS w hw).obj U) s)) :=
  (transitionHom_base_apply B S hS Yi f D w hw i j v vi vj hvj hwvj hi hj hi' hj' U
        (etaleSectInv B S hS (w ≫ vi) hwvi (D.F i) U s)).trans
    (congrArg (fun z => etaleSect B S hS vj hvj (D.F j)
          ((smallEtalePostcomp B S hS w hw).obj U)
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app
          (.op ((smallEtalePostcomp B S hS w hw).obj U)) z))
      (etaleSect_compIso_inv_etaleSectInv B S hS w hw vi hvi hwvi (D.F i) U s))

/-! ### The transition as a morphism of the étale restrictions -/

/-- **The transition of a descent datum on a test space, as a morphism of the étale restrictions
of the two component modules to that space.**  This is the reading
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` bundled: a morphism of sheaves of
modules on the test space, whose component over a chart is the reading over that chart.

It is the form in which the reading is presheaf data on the charts of the members: naturality in
the chart is naturality of a morphism of sheaves of modules and so costs nothing, where
`.transitionSect_restrict` has to be proved. -/
def transitionEtaleForm (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj) :
    (etaleModulePullback.{u, u} B S hS vi hvi).obj (D.F i) ⟶
      (etaleModulePullback.{u, u} B S hS vj hvj).obj (D.F j) :=
  (modulePullbackIsoEtaleModulePullback B S hS vi hvi).inv.app (D.F i) ≫
    transitionHom B S hS Yi f D i j v vi vj hi hj ≫
    (modulePullbackIsoEtaleModulePullback B S hS vj hvj).hom.app (D.F j)

/-- A morphism of modules equal to a composite of three, read on a section.  The four morphisms
are variables, which is what lets a consumer cross from the composite spelling to its own in one
definitional step. -/
theorem val_app_trans₃_apply {D₀ : AlgebraicSpaces B S hS}
    {P Q R W : Modules.{u, u} B S hS D₀.1 D₀.2} (α : P ⟶ Q) (β : Q ⟶ R) (γ : R ⟶ W)
    (θ : P ⟶ W) (hθ : θ = α ≫ β ≫ γ) (U : SmallEtale B S hS D₀.1)
    (m : P.val.obj (.op U)) :
    θ.val.app (.op U) m =
      γ.val.app (.op U) (β.val.app (.op U) (α.val.app (.op U) m)) :=
  hθ ▸ rfl

/-- The étale restriction of a morphism of modules, read on a section over a chart of the source:
restriction along an étale morphism is restriction of charts, so it is that morphism read over
the composite chart.  Stated on variables. -/
theorem etaleModulePullback_map_val_app_apply {T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T)
    (hw : IsEtale B S hS w.hom) {P Q : Modules.{u, u} B S hS T.1 T.2} (θ : P ⟶ Q)
    (U : SmallEtale B S hS T'.1) (m : P.val.obj (.op ((smallEtalePostcomp B S hS w hw).obj U))) :
    ((etaleModulePullback.{u, u} B S hS w hw).map θ).val.app (.op U) m =
      θ.val.app (.op ((smallEtalePostcomp B S hS w hw).obj U)) m := rfl

/-- A morphism of modules which is the component of an isomorphism equal to the identity is the
identity.  Stated on variables. -/
theorem hom_eq_id_of_refl {D₀ : AlgebraicSpaces B S hS} {P : Modules.{u, u} B S hS D₀.1 D₀.2}
    {e : P ≅ P} (h : e = Iso.refl P) (ψ : P ⟶ P) (hψ : ψ = e.hom) : ψ = 𝟙 P :=
  hψ.trans (congrArg Iso.hom h)

/-- An isomorphism conjugating the identity is the identity.  Stated on variables, so that the
conjugate never has to be matched against a concrete term. -/
theorem inv_comp_comp_hom_eq_id {D₀ : AlgebraicSpaces B S hS}
    {P Q : Modules.{u, u} B S hS D₀.1 D₀.2} (e : P ≅ Q) (ψ : P ⟶ P) (hψ : ψ = 𝟙 P)
    (θ : Q ⟶ Q) (hθ : θ = e.inv ≫ ψ ≫ e.hom) : θ = 𝟙 Q := by
  subst hψ hθ
  simp

/-- **The transition of a descent datum from a member to itself is the identity morphism of the
étale restriction.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_id` at the level of morphisms of
sheaves of modules, where it is `map_id` of the presheaf to be assembled. -/
theorem transitionEtaleForm_id (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS}
    (i : I) (v : T ⟶ pair B S hS Yi f i i) (w : T ⟶ Yi i) (hw : IsEtale B S hS w.hom)
    (hi : v ≫ pairFst B S hS Yi f i i = w) (hj : v ≫ pairSnd B S hS Yi f i i = w) :
    transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj =
      𝟙 ((etaleModulePullback.{u, u} B S hS w hw).obj (D.F i)) :=
  inv_comp_comp_hom_eq_id B S hS
    ((modulePullbackIsoEtaleModulePullback B S hS w hw).app (D.F i))
    (transitionHom B S hS Yi f D i i v w w hi hj)
    (hom_eq_id_of_refl B S hS (transitionOn_refl B S hS Yi f D i v w hi hj)
      (transitionHom B S hS Yi f D i i v w w hi hj) rfl)
    (transitionEtaleForm B S hS Yi f D i i v w w hw hw hi hj) rfl

/-- Two morphisms of modules which are the components of two isomorphisms composing to a third
compose to the component of that third.  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.hom_val_app_comp_congr` before the morphisms are
read on a section; as there, the three are variables identified with the three components by
hypotheses. -/
theorem hom_comp_congr {D₀ : AlgebraicSpaces B S hS}
    {P Q R : Modules.{u, u} B S hS D₀.1 D₀.2} {e : P ≅ Q} {e' : Q ≅ R} {e'' : P ≅ R}
    (h : e ≪≫ e' = e'') (ψ : P ⟶ Q) (ψ' : Q ⟶ R) (ψ'' : P ⟶ R)
    (hψ : ψ = e.hom) (hψ' : ψ' = e'.hom) (hψ'' : ψ'' = e''.hom) : ψ ≫ ψ' = ψ'' := by
  subst hψ hψ' hψ''
  rw [← h]
  rfl

/-- Three isomorphisms conjugating a composable pair of morphisms carry their composite to the
composite of the conjugates.  Stated on variables. -/
theorem etaleForm_comp_congr {D₀ : AlgebraicSpaces B S hS}
    {P P' Q Q' R R' : Modules.{u, u} B S hS D₀.1 D₀.2} (ei : P ≅ P') (ej : Q ≅ Q') (ek : R ≅ R')
    (ψij : P ⟶ Q) (ψjk : Q ⟶ R) (ψik : P ⟶ R) (h : ψij ≫ ψjk = ψik)
    (θij : P' ⟶ Q') (θjk : Q' ⟶ R') (θik : P' ⟶ R')
    (hij : θij = ei.inv ≫ ψij ≫ ej.hom) (hjk : θjk = ej.inv ≫ ψjk ≫ ek.hom)
    (hik : θik = ei.inv ≫ ψik ≫ ek.hom) : θij ≫ θjk = θik := by
  subst hij hjk hik h
  simp

/-- **The transition of a descent datum composes across three members, as morphisms of the étale
restrictions.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_comp` at the level of morphisms of
sheaves of modules, where it is the composition half of `map_comp` of the presheaf to be
assembled; the other half is the change of test space, which has no morphism-level form — see the
implementation notes. -/
theorem transitionEtaleForm_comp (D : DescentDatum B S hS Yi f) (i j k : I)
    (T : AlgebraicSpaces B S hS) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (vk : T ⟶ Yi k)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom) (hvk : IsEtale B S hS vk.hom)
    (vij : T ⟶ pair B S hS Yi f i j) (vjk : T ⟶ pair B S hS Yi f j k)
    (vik : T ⟶ pair B S hS Yi f i k)
    (hij₀ : vij ≫ pairFst B S hS Yi f i j = vi) (hij₁ : vij ≫ pairSnd B S hS Yi f i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Yi f j k = vj) (hjk₁ : vjk ≫ pairSnd B S hS Yi f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS Yi f i k = vi) (hik₁ : vik ≫ pairSnd B S hS Yi f i k = vk) :
    transitionEtaleForm B S hS Yi f D i j vij vi vj hvi hvj hij₀ hij₁ ≫
        transitionEtaleForm B S hS Yi f D j k vjk vj vk hvj hvk hjk₀ hjk₁ =
      transitionEtaleForm B S hS Yi f D i k vik vi vk hvi hvk hik₀ hik₁ :=
  etaleForm_comp_congr B S hS
    ((modulePullbackIsoEtaleModulePullback B S hS vi hvi).app (D.F i))
    ((modulePullbackIsoEtaleModulePullback B S hS vj hvj).app (D.F j))
    ((modulePullbackIsoEtaleModulePullback B S hS vk hvk).app (D.F k))
    (transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁)
    (transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁)
    (transitionHom B S hS Yi f D i k vik vi vk hik₀ hik₁)
    (hom_comp_congr B S hS
      (D.cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)
      (transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁)
      (transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁)
      (transitionHom B S hS Yi f D i k vik vi vk hik₀ hik₁) rfl rfl rfl)
    (transitionEtaleForm B S hS Yi f D i j vij vi vj hvi hvj hij₀ hij₁)
    (transitionEtaleForm B S hS Yi f D j k vjk vj vk hvj hvk hjk₀ hjk₁)
    (transitionEtaleForm B S hS Yi f D i k vik vi vk hvi hvk hik₀ hik₁) rfl rfl rfl

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
