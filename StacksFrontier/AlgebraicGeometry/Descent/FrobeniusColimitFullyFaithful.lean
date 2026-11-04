module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitHomReduction
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageHomModule
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeFilteredColimits

/-!
# Full faithfulness of the comparison functor of Stacks Tag 0EXB, from one colimit

Let `p` be a prime and let `X` be a quasi-compact quasi-separated scheme in characteristic `p`.
Write `φ` for the `p`-th power endomorphism of `𝒪_X`, `S_φ` and `U_φ` for extension and
restriction of scalars along it, and `S_n`, `U_n` for extension and restriction of scalars along
the stage-`n` coprojection `𝒪_X ⟶ colim_F 𝒪_X`. This file proves that **the comparison functor
of Tag 0EXB is fully faithful as soon as the cocone of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictDiagram` is colimiting**, i.e. as
soon as

`U_n (S_n 𝒢) = colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`

for every `n` and every sheaf of `𝒪_X`-modules `𝒢`. That identification is the one remaining
input to this half of Tag 0EXB, and it is taken here as an explicit hypothesis: nothing else
beyond the hypotheses Tag 0EXB itself carries is assumed.

The argument is the interchange of two colimits. Applying `Hom_{𝒪_X}(ℰ, -)`, which commutes with
filtered colimits for `ℰ` finite locally free on a quasi-compact quasi-separated scheme
(`Stacks.FiniteLocallyFree.preservesFilteredColimits_coyoneda_of_isFiniteLocallyFree`), to the
hypothesised colimit gives

`Hom_{𝒪_X}(ℰ, U_n (S_n 𝒢)) = colim_j Hom_{𝒪_X}(ℰ, (U_φ)^{∘j}((S_φ)^{∘j}𝒢))`.

The left-hand side is `Hom_{colim_F 𝒪_X}(S_n ℰ, S_n 𝒢)` by the stage-`n` adjunction, each term of
the right-hand side is `Hom_{𝒪_X}((S_φ)^{∘j}ℰ, (S_φ)^{∘j}𝒢)` by
`AlgebraicGeometry.homEquiv_frobeniusRestrictExtendIter`, and the resulting map between the
colimits is the comparison of Tag 0EXB by
`AlgebraicGeometry.homEquiv_comp_frobeniusStageRestrictLeg`. Surjectivity and injectivity of the
comparison are then joint surjectivity of the legs of a colimit of types and the description of
when two elements of a filtered colimit of types agree.

## Main results

* `AlgebraicGeometry.exists_frobeniusStageModuleHomMap_eq` and
  `AlgebraicGeometry.exists_heq_endoRaise_of_frobeniusStageModuleHomMap_eq`: **surjectivity and
  injectivity of the comparison on Hom-sets, at the level of all `𝒪_X`-modules.**
* `AlgebraicGeometry.exists_frobeniusStageHomMap_eq` and
  `AlgebraicGeometry.agree_of_frobeniusStageHomMap_eq`: the same two statements for `Vect(X)`, in
  the exact shape
  `AlgebraicGeometry.faithful_frobeniusColimitVectComparison_of_stageHomMap` consumes them in.
* `AlgebraicGeometry.faithful_frobeniusColimitVectComparison_of_isColimit` and
  `AlgebraicGeometry.full_frobeniusColimitVectComparison_of_isColimit`: **the comparison functor
  of Tag 0EXB is faithful, respectively full, as soon as the cocone of Tag 0EXB is colimiting.**

## Implementation notes

The hypothesis is `∀ n 𝒢, IsColimit (frobeniusStageRestrictCocone X p hX n 𝒢)` and nothing else:
the two results below carry it, and they carry it as a hypothesis rather than discharging it,
because it is unproved. **Neither is the unconditional full faithfulness of the comparison
functor of Tag 0EXB**, and neither should be read as it.

Two universe points. The diagram is indexed by `ℕ`, which lives in `Type 0`, whereas
`Stacks.FiniteLocallyFree.preservesFilteredColimits_coyoneda_of_isFiniteLocallyFree` is stated
for a shape in `Type u` with morphisms in `Type u`; the bridge is
`CategoryTheory.Limits.preservesSmallestFilteredColimits_of_preservesFilteredColimits`, which
descends preservation of filtered colimits of any size to size `0`, and `ℕ` is filtered because
it is a nonempty join-semilattice. And `coyoneda` is taken over
`AlgebraicGeometry.Scheme.Modules`, which is `SheafOfModules.{u} X.ringCatSheaf`, while the
diagram lives over `AlgebraicGeometry.Scheme.ringSheafOnOpens`, a re-typing of the same sheaf of
rings; the two categories are the same up to unfolding those definitions, so the preservation
statement is applied through `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`
rather than by instance resolution, which does not unfold them.

The exponent bookkeeping is the one of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitCategory`:
`CategoryTheory.EndoColim.HomRep.Agree` asks for the two presentations to agree after being
raised to a *common* level, and the common level the colimit of types produces is an arbitrary
one, so the two raised morphisms have equal and not definitionally equal types. They are compared
by `HEq`, which `CategoryTheory.EndoColim.HomRep.agree_of_heq` turns into the transported
equality `Agree` asks for; this avoids transporting a morphism of `Vect(X)`, where neither `rw`
nor `simp` fires.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius

universe v v₂ u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Conjugating a morphism by two transports and then by their inverses leaves it alone.** -/
lemma eqToHom_comp_eqToHom_conj_comp_eqToHom {P P' Q Q' : C} (a : P = P') (b : Q = Q')
    (u : P' ⟶ Q') :
    eqToHom a.symm ≫ (eqToHom a ≫ u ≫ eqToHom b.symm) ≫ eqToHom b = u := by
  subst a; subst b; simp

/-- **Two morphisms conjugated by the same pair of transports are equal only if they are.** -/
lemma eq_of_eqToHom_conj_eq {P P' Q Q' : C} (a : P = P') (b : Q = Q') {x y : P ⟶ Q}
    (h : eqToHom a.symm ≫ x ≫ eqToHom b = eqToHom a.symm ≫ y ≫ eqToHom b) : x = y := by
  subst a; subst b; simpa using h

/-- A transported morphism between iterates of an endofunctor is heterogeneously equal to the
morphism it transports. -/
lemma endoHomCast_heq {F : C ⥤ C} {E G : C} {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) : HEq (endoHomCast hm hn f) f :=
  cast_heq _ f

/-- **Two presentations whose raises to a common level are heterogeneously equal, agree.** The
levels the two raises land at are equal and not definitionally equal, so the equality
`CategoryTheory.EndoColim.HomRep.Agree` asks for is one between transported morphisms; `HEq`
records it without naming the transports. -/
lemma EndoColim.HomRep.agree_of_heq {F : C ⥤ C} {A B : EndoColim F} {k l : ℕ}
    {f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj}
    {g : (F.endoIter (B.stage + l)).obj A.obj ⟶ (F.endoIter (A.stage + l)).obj B.obj}
    (j i : ℕ) (hji : k + j = l + i) (h : HEq (endoRaise f j) (endoRaise g i)) :
    HomRep.Agree (⟨k, f⟩ : HomRep A B) ⟨l, g⟩ :=
  ⟨j, i, hji, eq_of_heq (((endoHomCast_heq _ _ _).trans h).trans (endoHomCast_heq _ _ _).symm)⟩

/-- **The image of a cocone under `Hom(A, -)` has for legs the composition with the legs.** -/
lemma Limits.coyoneda_mapCocone_ι_app_apply {J : Type u₂} [Category.{v₂} J] {D : J ⥤ C}
    (c : Cocone D) (A : C) (j : J) (y : A ⟶ D.obj j) :
    ((coyoneda.obj (op A)).mapCocone c).ι.app j y = y ≫ c.ι.app j :=
  rfl

/-- **The unit of the `j + 1`-fold iterated adjunction applied to a morphism of the `j + 1`-fold
left adjoints is the unit of the `j`-fold one applied to the morphism of the `j`-fold left
adjoints, followed by the transition morphism.** This is the compatibility of the adjunction
isomorphisms `Hom(E, R^j L^j G) ≅ Hom(L^j E, L^j G)` with the transition morphisms of the diagram
of Stacks Tag 0EXB. -/
lemma Adjunction.homEquiv_endoIter_map {L R : C ⥤ C} (adj : L ⊣ R) (i : ℕ) {E G : C}
    (f : (L.endoIter i).obj E ⟶ (L.endoIter i).obj G) :
    (adj.endoIter (i + 1)).homEquiv E ((L.endoIter (i + 1)).obj G) (L.map f) =
      (adj.endoIter i).homEquiv E ((L.endoIter i).obj G) f ≫
        ((R.endoIter i).map (adj.unit.app ((L.endoIter i).obj G)) ≫
          eqToHom (R.endoIter_obj_obj i ((L.endoIter (i + 1)).obj G))) := by
  have hnat : adj.unit.app ((L.endoIter i).obj E) ≫ R.map (L.map f) =
      f ≫ adj.unit.app ((L.endoIter i).obj G) := (adj.unit.naturality f).symm
  have key := Functor.endoIter_map_comp_eqToHom_comp R i
    (adj.unit.app ((L.endoIter i).obj E)) (L.map f)
    (adj.unit.app ((L.endoIter i).obj E) ≫ R.map (L.map f)) rfl (by simp) rfl
    (R.endoIter_obj_obj i ((L.endoIter (i + 1)).obj G))
  rw [hnat, Functor.map_comp, eqToHom_refl, Category.comp_id] at key
  have hL : (adj.endoIter (i + 1)).homEquiv E ((L.endoIter (i + 1)).obj G) (L.map f) =
      (adj.endoIter (i + 1)).unit.app E ≫ (R.endoIter (i + 1)).map (L.map f) := rfl
  have hR : (adj.endoIter i).homEquiv E ((L.endoIter i).obj G) f =
      (adj.endoIter i).unit.app E ≫ (R.endoIter i).map f := rfl
  refine hL.trans (Eq.trans ?_ (congrArg (fun q ↦ q ≫
    ((R.endoIter i).map (adj.unit.app ((L.endoIter i).obj G)) ≫
      eqToHom (R.endoIter_obj_obj i ((L.endoIter (i + 1)).obj G)))) hR.symm))
  refine Eq.trans (congrArg (fun q ↦ q ≫ (R.endoIter (i + 1)).map (L.map f))
    (Adjunction.endoIter_unit_app_succ adj i E)) ?_
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  exact congrArg (fun q ↦ (adj.endoIter i).unit.app E ≫ q) (key.trans (Category.assoc _ _ _))

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-! ### The adjunction isomorphisms and the transition morphisms of the diagram -/

/-- **One transition morphism of the diagram of Stacks Tag 0EXB, read through the `j`-fold
adjunction**: a morphism of the `j`-fold extensions of scalars along Frobenius, extended once
more and read as a morphism into the `j + 1`-st term of the diagram, is the same morphism read
into the `j`-th term followed by the transition morphism. -/
lemma homEquiv_frobeniusRestrictExtendIter_map (j : ℕ)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G) :
    homEquiv_frobeniusRestrictExtendIter X p hX (j + 1) E G
        ((frobeniusExtendScalars X p hX).map f) =
      homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫
        frobeniusRestrictExtendIterMap X p hX j G :=
  Adjunction.homEquiv_endoIter_map (frobeniusExtendScalarsAdjunction X p hX) j f

/-- **Arbitrarily many transition morphisms of the diagram of Stacks Tag 0EXB, read through the
adjunctions**: raising a morphism of the `j`-fold extensions of scalars along Frobenius `m` times
and reading it into the `j + m`-th term of the diagram is reading it into the `j`-th term and
following it with the transition from `j` to `j + m`. -/
lemma homEquiv_frobeniusRestrictExtendIter_endoRaise (j m : ℕ)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G) :
    homEquiv_frobeniusRestrictExtendIter X p hX (j + m) E G
        (endoRaise (F := frobeniusExtendScalars X p hX) f m) =
      homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫
        (frobeniusRestrictExtendDiagram X p hX G).map (homOfLE (Nat.le_add_right j m)) := by
  induction m with
  | zero =>
      have h0 : (frobeniusRestrictExtendDiagram X p hX G).map
            (homOfLE (Nat.le_add_right j 0)) =
          𝟙 (frobeniusRestrictExtendIter X p hX j G) :=
        (congrArg (frobeniusRestrictExtendDiagram X p hX G).map
          (Subsingleton.elim (homOfLE (Nat.le_add_right j 0)) (𝟙 j))).trans
            ((frobeniusRestrictExtendDiagram X p hX G).map_id j)
      exact ((congrArg (fun q ↦ homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫ q)
        h0).trans (Category.comp_id _)).symm
  | succ m ih =>
      have hstep : (frobeniusRestrictExtendDiagram X p hX G).map
            (homOfLE (Nat.le_add_right j m)) ≫
            frobeniusRestrictExtendIterMap X p hX (j + m) G =
          (frobeniusRestrictExtendDiagram X p hX G).map
            (homOfLE (Nat.le_add_right j (m + 1))) :=
        (congrArg (fun q ↦ (frobeniusRestrictExtendDiagram X p hX G).map
              (homOfLE (Nat.le_add_right j m)) ≫ q)
            (frobeniusRestrictExtendDiagram_map_succ X p hX G (j + m)).symm).trans
          (((frobeniusRestrictExtendDiagram X p hX G).map_comp
              (homOfLE (Nat.le_add_right j m))
              (homOfLE (Nat.le_add_right (j + m) 1))).symm.trans
            (congrArg (frobeniusRestrictExtendDiagram X p hX G).map (Subsingleton.elim _ _)))
      refine Eq.trans (homEquiv_frobeniusRestrictExtendIter_map X p hX (j + m) E G
        (endoRaise (F := frobeniusExtendScalars X p hX) f m)) ?_
      refine Eq.trans (congrArg (fun q ↦ q ≫ frobeniusRestrictExtendIterMap X p hX (j + m) G)
        ih) ?_
      exact (Category.assoc _ _ _).trans
        (congrArg (fun q ↦ homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫ q) hstep)

/-- `AlgebraicGeometry.homEquiv_frobeniusRestrictExtendIter_endoRaise` at an arbitrary morphism
of the index category, the raised morphism being transported to the level that morphism lands
at. -/
lemma homEquiv_frobeniusRestrictExtendIter_endoHomCast_endoRaise (j m N : ℕ) (hN : j + m = N)
    (E G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (f : ((frobeniusExtendScalars X p hX).endoIter j).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter j).obj G) (a : j ⟶ N) :
    homEquiv_frobeniusRestrictExtendIter X p hX N E G
        (endoHomCast (F := frobeniusExtendScalars X p hX) hN hN
          (endoRaise (F := frobeniusExtendScalars X p hX) f m)) =
      homEquiv_frobeniusRestrictExtendIter X p hX j E G f ≫
        (frobeniusRestrictExtendDiagram X p hX G).map a := by
  subst hN
  rw [endoHomCast_rfl, Subsingleton.elim a (homOfLE (Nat.le_add_right j m))]
  exact homEquiv_frobeniusRestrictExtendIter_endoRaise X p hX j m E G f

/-! ### Raising at the level of `Vect(X)` and at the level of all modules -/

/-- **Raising a morphism of the `j`-fold Frobenius pullbacks of finite locally free modules is
raising the morphism of the `j`-fold extensions of scalars it underlies.** -/
lemma frobeniusPullbackIterHom_endoRaise (c m : ℕ) {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX c).obj E ⟶ (frobeniusPullbackIter X p hX c).obj G) :
    frobeniusPullbackIterHom X p hX (c + m)
        (endoRaise (F := frobeniusPullback X p hX) f m) =
      endoRaise (F := frobeniusExtendScalars X p hX)
        (frobeniusPullbackIterHom X p hX c f) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      refine Eq.trans ?_ (congrArg (fun q ↦ (frobeniusExtendScalars X p hX).map q) ih)
      exact Functor.map_eqToHom_conj_eq (pullback_absoluteFrobenius_eq X p hX)
        (ι_frobeniusPullbackIter_obj X p hX (c + m) E)
        (ι_frobeniusPullbackIter_obj X p hX (c + m) G)
        (endoRaise (F := frobeniusPullback X p hX) f m).hom
        (ι_frobeniusPullbackIter_obj X p hX (c + m + 1) E)
        (ι_frobeniusPullbackIter_obj X p hX (c + m + 1) G)

/-- Reading a morphism of the `j`-fold Frobenius pullbacks as a morphism of the `j`-fold
extensions of scalars loses nothing. -/
lemma frobeniusPullbackIterHom_injective (c : ℕ) {E G : X.Vect}
    {f g : (frobeniusPullbackIter X p hX c).obj E ⟶ (frobeniusPullbackIter X p hX c).obj G}
    (h : frobeniusPullbackIterHom X p hX c f = frobeniusPullbackIterHom X p hX c g) : f = g :=
  ObjectProperty.hom_ext _ (eq_of_eqToHom_conj_eq
    (ι_frobeniusPullbackIter_obj X p hX c E) (ι_frobeniusPullbackIter_obj X p hX c G) h)

/-- **Two morphisms of Frobenius pullbacks of finite locally free modules whose underlying
morphisms of modules are heterogeneously equal are heterogeneously equal.** -/
lemma heq_of_frobeniusPullbackIterHom_heq {c c' : ℕ} (hc : c = c') {E G : X.Vect}
    (f : (frobeniusPullbackIter X p hX c).obj E ⟶ (frobeniusPullbackIter X p hX c).obj G)
    (g : (frobeniusPullbackIter X p hX c').obj E ⟶ (frobeniusPullbackIter X p hX c').obj G)
    {f' : ((frobeniusExtendScalars X p hX).endoIter c).obj E.obj ⟶
      ((frobeniusExtendScalars X p hX).endoIter c).obj G.obj}
    {g' : ((frobeniusExtendScalars X p hX).endoIter c').obj E.obj ⟶
      ((frobeniusExtendScalars X p hX).endoIter c').obj G.obj}
    (hf : frobeniusPullbackIterHom X p hX c f = f')
    (hg : frobeniusPullbackIterHom X p hX c' g = g') (h : HEq f' g') : HEq f g := by
  subst hc; subst hf; subst hg
  exact heq_of_eq (frobeniusPullbackIterHom_injective X p hX c (eq_of_heq h))

/-! ### The colimit of Hom-sets -/

/-- **`Hom_{𝒪_X}(ℰ, -)` carries the cocone of Stacks Tag 0EXB to a colimit cocone of types**, for
`ℰ` a finite locally free module on a quasi-compact quasi-separated scheme. This is
[Stacks, Tag 01BS] applied to the diagram of Tag 0EXB. -/
noncomputable def isColimitCoyonedaMapCoconeFrobeniusStageRestrict [CompactSpace X]
    [QuasiSeparatedSpace X] (n : ℕ) (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (hcolim : IsColimit (frobeniusStageRestrictCocone X p hX n G)) :
    IsColimit ((coyoneda.obj (op E)).mapCocone (frobeniusStageRestrictCocone X p hX n G)) := by
  have hfilt : PreservesFilteredColimitsOfSize.{u, u} (coyoneda.obj (op E)) :=
    ⟨fun K _ _ ↦ have := hE
      Stacks.FiniteLocallyFree.preservesFilteredColimits_coyoneda_of_isFiniteLocallyFree X E K⟩
  have hsmall : PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (op E)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hshape : PreservesColimitsOfShape ℕ (coyoneda.obj (op E)) :=
    hsmall.preserves_filtered_colimits ℕ
  exact (hshape.preservesColimit.preserves hcolim).some

/-! ### Surjectivity and injectivity of the comparison on Hom-sets, on all modules -/

/-- **The comparison of Stacks Tag 0EXB on Hom-sets is surjective, at the level of all
`𝒪_X`-modules and at an arbitrarily large level of the colimit.** Every morphism
`S_n ℰ ⟶ S_n 𝒢` of `colim_F 𝒪_X`-modules is
`AlgebraicGeometry.frobeniusStageModuleHomMap` of a morphism of the `N`-fold extensions of
scalars along Frobenius, for some `N` at least a prescribed `c`.

The adjunct of the morphism is a morphism `ℰ ⟶ U_n (S_n 𝒢)` out of the finite locally free `ℰ`,
hence factors through a term of the diagram, by joint surjectivity of the legs of a colimit of
types; the level can be raised to pass `c` because the legs of a cocone are compatible with the
transitions. -/
theorem exists_frobeniusStageModuleHomMap_eq [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ)
    (E : X.Modules) (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (hcolim : IsColimit (frobeniusStageRestrictCocone X p hX n G))
    (w : (frobeniusStageExtendScalars X p hX n).obj E ⟶
      (frobeniusStageExtendScalars X p hX n).obj G) (c : ℕ) :
    ∃ N, c ≤ N ∧ ∃ f : ((frobeniusExtendScalars X p hX).endoIter N).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter N).obj G,
      frobeniusStageModuleHomMap X p hX n N f = w := by
  have hc := isColimitCoyonedaMapCoconeFrobeniusStageRestrict X p hX n E hE G hcolim
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc
    ((frobeniusStageExtendScalarsAdjunction X p hX n).homEquiv E _ w)
  refine ⟨c + j, Nat.le_add_right c j, ?_⟩
  refine ⟨(homEquiv_frobeniusRestrictExtendIter X p hX (c + j) E G).symm
    (y ≫ (frobeniusRestrictExtendDiagram X p hX G).map (homOfLE (Nat.le_add_left j c))), ?_⟩
  refine (frobeniusStageExtendScalarsAdjunction X p hX n).homEquiv E _ |>.injective ?_
  refine Eq.trans ?_ hy
  refine Eq.trans ?_ ((Limits.coyoneda_mapCocone_ι_app_apply
    (frobeniusStageRestrictCocone X p hX n G) E j y).symm)
  refine Eq.trans (homEquiv_comp_frobeniusStageRestrictLeg X p hX n (c + j) E G _).symm ?_
  refine Eq.trans (congrArg (fun q ↦ q ≫ frobeniusStageRestrictLeg X p hX n (c + j) G)
    ((homEquiv_frobeniusRestrictExtendIter X p hX (c + j) E G).apply_symm_apply _)) ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun q ↦ y ≫ q)
    ((frobeniusStageRestrictCocone X p hX n G).w (homOfLE (Nat.le_add_left j c))))

/-- **The comparison of Stacks Tag 0EXB on Hom-sets is injective on the colimit, at the level of
all `𝒪_X`-modules.** Two morphisms of iterated extensions of scalars along Frobenius with the
same image under `AlgebraicGeometry.frobeniusStageModuleHomMap` become equal after being raised
to a common level — which is what it means for the map out of the colimit of the Hom-sets to be
injective.

The two adjuncts are morphisms out of the finite locally free `ℰ` into the colimit of the diagram
with the same image, hence agree at some level of the diagram; the levels the two raises land at
are only propositionally equal, so the conclusion is recorded as a `HEq`. -/
theorem exists_heq_endoRaise_of_frobeniusStageModuleHomMap_eq [CompactSpace X]
    [QuasiSeparatedSpace X] (n : ℕ) (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (hcolim : IsColimit (frobeniusStageRestrictCocone X p hX n G)) (c d : ℕ)
    (f : ((frobeniusExtendScalars X p hX).endoIter c).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter c).obj G)
    (g : ((frobeniusExtendScalars X p hX).endoIter d).obj E ⟶
      ((frobeniusExtendScalars X p hX).endoIter d).obj G)
    (h : frobeniusStageModuleHomMap X p hX n c f = frobeniusStageModuleHomMap X p hX n d g) :
    ∃ m m' : ℕ, c + m = d + m' ∧
      HEq (endoRaise (F := frobeniusExtendScalars X p hX) f m)
        (endoRaise (F := frobeniusExtendScalars X p hX) g m') := by
  have hc := isColimitCoyonedaMapCoconeFrobeniusStageRestrict X p hX n E hE G hcolim
  have hleg : ((coyoneda.obj (op E)).mapCocone
        (frobeniusStageRestrictCocone X p hX n G)).ι.app c
        (homEquiv_frobeniusRestrictExtendIter X p hX c E G f) =
      ((coyoneda.obj (op E)).mapCocone
        (frobeniusStageRestrictCocone X p hX n G)).ι.app d
        (homEquiv_frobeniusRestrictExtendIter X p hX d E G g) :=
    (homEquiv_comp_frobeniusStageRestrictLeg X p hX n c E G f).trans
      ((congrArg (fun q ↦ (frobeniusStageExtendScalarsAdjunction X p hX n).unit.app E ≫
          (frobeniusStageRestrictScalars X p hX n).map q) h).trans
        (homEquiv_comp_frobeniusStageRestrictLeg X p hX n d E G g).symm)
  obtain ⟨N, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hleg
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom a)
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le (leOfHom b)
  refine ⟨m, m', hm', ?_⟩
  have hcast : endoHomCast (F := frobeniusExtendScalars X p hX) rfl rfl
        (endoRaise (F := frobeniusExtendScalars X p hX) f m) =
      endoHomCast (F := frobeniusExtendScalars X p hX) hm'.symm hm'.symm
        (endoRaise (F := frobeniusExtendScalars X p hX) g m') :=
    (homEquiv_frobeniusRestrictExtendIter X p hX (c + m) E G).injective
      ((homEquiv_frobeniusRestrictExtendIter_endoHomCast_endoRaise X p hX c m (c + m) rfl
          E G f a).trans
        (hab.trans (homEquiv_frobeniusRestrictExtendIter_endoHomCast_endoRaise X p hX d m'
          (c + m) hm'.symm E G g b).symm))
  exact ((endoHomCast_heq (F := frobeniusExtendScalars X p hX) rfl rfl _).symm.trans
    (heq_of_eq hcast)).trans (endoHomCast_heq _ _ _)

/-! ### Surjectivity and injectivity of the comparison on Hom-sets, on `Vect(X)` -/

/-- **The comparison of Stacks Tag 0EXB on Hom-sets is surjective**, in the shape
`AlgebraicGeometry.full_frobeniusColimitVectComparison_of_stageHomMap` consumes it in: every
morphism `S_n ℰ ⟶ S_n 𝒢` of finite locally free `colim_F 𝒪_X`-modules is
`AlgebraicGeometry.frobeniusStageHomMap` of a morphism of the `n + k`-fold Frobenius pullbacks,
for some `k`. -/
theorem exists_frobeniusStageHomMap_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (hcolim : ∀ (n : ℕ) (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens),
      IsColimit (frobeniusStageRestrictCocone X p hX n G))
    (n : ℕ) (E G : X.Vect)
    (w : (frobeniusStageFunctor X p hX n).obj E ⟶ (frobeniusStageFunctor X p hX n).obj G) :
    ∃ (k : ℕ) (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
      (frobeniusPullbackIter X p hX (n + k)).obj G),
      frobeniusStageHomMap X p hX n (n + k) f = w := by
  obtain ⟨N, hN, f, hf⟩ := exists_frobeniusStageModuleHomMap_eq X p hX n E.obj E.2 G.obj
    (hcolim n G.obj) w.hom n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨k, ObjectProperty.homMk
    (eqToHom (ι_frobeniusPullbackIter_obj X p hX (n + k) E) ≫ f ≫
      eqToHom (ι_frobeniusPullbackIter_obj X p hX (n + k) G).symm), ?_⟩
  refine ObjectProperty.hom_ext _ ((frobeniusStageHomMap_hom X p hX n (n + k) _).trans ?_)
  refine Eq.trans (congrArg (fun q ↦ frobeniusStageModuleHomMap X p hX n (n + k)
      (E := E.obj) (G := G.obj) q) ?_) hf
  exact eqToHom_comp_eqToHom_conj_comp_eqToHom
    (ι_frobeniusPullbackIter_obj X p hX (n + k) E)
    (ι_frobeniusPullbackIter_obj X p hX (n + k) G) f

/-- **The comparison of Stacks Tag 0EXB on Hom-sets is injective on the colimit**, in the shape
`AlgebraicGeometry.faithful_frobeniusColimitVectComparison_of_stageHomMap` consumes it in: two
presentations of morphisms `(ℰ, n) ⟶ (𝒢, n)` with the same image under
`AlgebraicGeometry.frobeniusStageHomMap` agree in the sense of
`CategoryTheory.EndoColim.HomRep.Agree`. -/
theorem agree_of_frobeniusStageHomMap_eq [CompactSpace X] [QuasiSeparatedSpace X]
    (hcolim : ∀ (n : ℕ) (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens),
      IsColimit (frobeniusStageRestrictCocone X p hX n G))
    (n k l : ℕ) (E G : X.Vect)
    (f : (frobeniusPullbackIter X p hX (n + k)).obj E ⟶
      (frobeniusPullbackIter X p hX (n + k)).obj G)
    (g : (frobeniusPullbackIter X p hX (n + l)).obj E ⟶
      (frobeniusPullbackIter X p hX (n + l)).obj G)
    (hfg : frobeniusStageHomMap X p hX n (n + k) f = frobeniusStageHomMap X p hX n (n + l) g) :
    EndoColim.HomRep.Agree
      (⟨k, f⟩ : EndoColim.HomRep (⟨E, n⟩ : frobeniusColimitVectModel X p hX) ⟨G, n⟩) ⟨l, g⟩ := by
  have hmod : frobeniusStageModuleHomMap X p hX n (n + k)
        (frobeniusPullbackIterHom X p hX (n + k) f) =
      frobeniusStageModuleHomMap X p hX n (n + l)
        (frobeniusPullbackIterHom X p hX (n + l) g) :=
    (frobeniusStageHomMap_hom X p hX n (n + k) f).symm.trans
      ((congrArg (fun q ↦ q.hom) hfg).trans (frobeniusStageHomMap_hom X p hX n (n + l) g))
  obtain ⟨m, m', hmm, hheq⟩ := exists_heq_endoRaise_of_frobeniusStageModuleHomMap_eq X p hX n
    E.obj E.2 G.obj (hcolim n G.obj) (n + k) (n + l)
    (frobeniusPullbackIterHom X p hX (n + k) f)
    (frobeniusPullbackIterHom X p hX (n + l) g) hmod
  refine EndoColim.HomRep.agree_of_heq m m' (by omega) ?_
  exact heq_of_frobeniusPullbackIterHom_heq X p hX (by omega) _ _
    (frobeniusPullbackIterHom_endoRaise X p hX (n + k) m f)
    (frobeniusPullbackIterHom_endoRaise X p hX (n + l) m' g) hheq

/-! ### Full faithfulness of the comparison functor -/

/-- **The comparison functor of Stacks Tag 0EXB is faithful as soon as the cocone of Tag 0EXB is
colimiting.** The hypothesis is the identification
`U_n (S_n 𝒢) = colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`, and it is the only one beyond those Tag 0EXB
itself carries. **This is not the unconditional faithfulness of the comparison functor**, which
needs that identification and does not have it. -/
theorem faithful_frobeniusColimitVectComparison_of_isColimit [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hcolim : ∀ (n : ℕ) (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens),
      IsColimit (frobeniusStageRestrictCocone X p hX n G)) :
    (frobeniusColimitVectComparison X p hX).Faithful :=
  faithful_frobeniusColimitVectComparison_of_stageHomMap X p hX
    (fun n k l E G f g hfg ↦ agree_of_frobeniusStageHomMap_eq X p hX hcolim n k l E G f g hfg)
    (fun n E G w ↦ exists_frobeniusStageHomMap_eq X p hX hcolim n E G w)

/-- **The comparison functor of Stacks Tag 0EXB is full as soon as the cocone of Tag 0EXB is
colimiting.** The hypothesis is the identification
`U_n (S_n 𝒢) = colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`, and it is the only one beyond those Tag 0EXB
itself carries. **This is not the unconditional fullness of the comparison functor**, which needs
that identification and does not have it. -/
theorem full_frobeniusColimitVectComparison_of_isColimit [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hcolim : ∀ (n : ℕ) (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens),
      IsColimit (frobeniusStageRestrictCocone X p hX n G)) :
    (frobeniusColimitVectComparison X p hX).Full :=
  full_frobeniusColimitVectComparison_of_stageHomMap X p hX
    (fun n k l E G f g hfg ↦ agree_of_frobeniusStageHomMap_eq X p hX hcolim n k l E G f g hfg)
    (fun n E G w ↦ exists_frobeniusStageHomMap_eq X p hX hcolim n E G w)

end AlgebraicGeometry

end
