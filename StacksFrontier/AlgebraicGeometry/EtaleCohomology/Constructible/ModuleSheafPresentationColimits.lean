module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafGenerationByQCQS
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.SmallEtaleFiniteCoverings
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules on the small étale site as filtered colimits of finite presentations

Every sheaf of `Λ`-modules on the small étale site of a quasi-compact quasi-separated scheme `X`
is a filtered colimit of sheaves carrying a *finite shriek presentation* by quasi-compact
quasi-separated étale objects: a cokernel of a map between two finite direct sums of the sheaves
`j_{U!}\underline{\Lambda}_U`. This is Stacks 093C for sheaves of modules, in the spelling
`AlgebraicGeometry.HasFiniteShriekPresentation`, and it is the hypothesis `h093C` of the library's
Stacks 03SA (3).

The proof is the one in the source, in three steps. First the sheaves
`j_{U!}\underline{\Lambda}_U` at quasi-compact quasi-separated objects generate, which is
Stacks 093B part (2) — `AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_qcqs` — so two
applications of it write the sheaf as the cokernel of a map `g` between two direct sums of them.
Second those generators are compact, which is where part (4) of Stacks 0738 enters through
`AlgebraicGeometry.isFinitelyPresentable_moduleShriekConstant`, so a map out of one into a direct
sum factors through a finite subsum and hence `g` restricts to maps between finite subsums. Third
the pairs of finite subsums compatible with `g` form a filtered poset and the cokernels of those
restrictions form a filtered diagram whose colimit is the cokernel of `g`.

The first two steps are stated for an arbitrary category here, since neither uses anything about
sheaves: a coproduct is the filtered colimit of the subcoproducts spanned by the finite subsets of
its index set, so a compact object maps into it only through a finite subcoproduct.

## Main results

* `CategoryTheory.Limits.exists_finiteSubcoproduct_factorization` — a morphism out of a finitely
  presentable object into a coproduct factors through a finite subcoproduct.
* `CategoryTheory.Limits.isSplitMono_finiteSubcoproductsCocone_ι` — the inclusion of a finite
  subcoproduct into the whole coproduct is a split monomorphism.
* `CategoryTheory.Limits.exists_finiteSubcoproduct_restriction` — a morphism of coproducts with
  compact source summands restricts to maps between finite subcoproducts.
* `CategoryTheory.Limits.exists_isFilteredColimit_cokernel_finiteSubcoproducts` — the cokernel of
  such a morphism is the filtered colimit of the cokernels of its restrictions.
* `AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations` — **Stacks 093C** for
  sheaves of `Λ`-modules on the small étale site, in the spelling
  `AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations`, which is the hypothesis
  `h093C` of `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf`
  (Stacks 03SA (3)).

## Implementation notes

The quasi-compactness and quasi-separatedness of `X` are carried as instance hypotheses, exactly
as Stacks 03SA carries them, and they enter at one point only: the compactness of
`j_{U!}\underline{\Lambda}_U` asks for
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`, which the library proves for a
quasi-compact quasi-separated `X`. Nothing else here needs them —
in particular the generation step, Stacks 093B part (2), does not.

`CoproductsFromFiniteFiltered.liftToFinsetObj` and
`CoproductsFromFiniteFiltered.finiteSubcoproductsCocone` are semireducible, so the definitional
comparisons the filtered-colimit proof rests on — that the value of the first at a finite subset is
the subcoproduct it spans, and that the vertex of the second is the whole coproduct — do not go
through at instance transparency. They are made reducible locally with
`attribute [local implicit_reducible]`, which is how
`StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModulePresentationColimits` handles the same
obstruction and changes no elaboration option.

The sheafification and the colimits of the sheaf category are supplied by the local instances
`AlgebraicGeometry.smallEtaleHasSheafifyModuleMax` and
`AlgebraicGeometry.smallEtaleHasColimitsOfSizeModuleMax`; both are propositions, so they agree
with whatever instances `AlgebraicGeometry.moduleShriekConstant` and
`AlgebraicGeometry.HasFiniteShriekPresentation` were elaborated with.

## References

* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe d a u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local implicit_reducible] CoproductsFromFiniteFiltered.liftToFinsetObj
  CoproductsFromFiniteFiltered.finiteSubcoproductsCocone

namespace CategoryTheory.Limits

open CoproductsFromFiniteFiltered

section Compact

variable {E : Type d} [Category.{a} E] [HasFiniteCoproducts E]

/-- **A morphism out of a compact object into a coproduct factors through a finite
subcoproduct.** A coproduct is the filtered colimit of the subcoproducts spanned by the finite
subsets of its index set, and a finitely presentable object sees that colimit. -/
public theorem exists_finiteSubcoproduct_factorization {A : Type a} (Y : A → E) [HasCoproduct Y]
    [HasColimitsOfShape (Finset (Discrete A)) E] (W : E) [IsFinitelyPresentable.{a} W]
    (f : W ⟶ ∐ Y) :
    ∃ (s : Finset (Discrete A)) (g : W ⟶ ∐ fun b : s => Y b.1.as),
      g ≫ Sigma.desc (fun b : s => Sigma.ι Y b.1.as) = f :=
  IsFinitelyPresentable.exists_hom_of_isColimit (isColimitFiniteSubproductsCocone Y) f

/-- **A morphism of coproducts restricts to the finite subcoproducts**, when the summands of the
source are compact: a finite subcoproduct of the source maps into some finite subcoproduct of the
target, compatibly with the given morphism. -/
public theorem exists_finiteSubcoproduct_restriction {A B : Type a} (X : A → E) (Y : B → E)
    [HasCoproduct X] [HasCoproduct Y] [HasColimitsOfShape (Finset (Discrete B)) E]
    (hcompact : ∀ i, IsFinitelyPresentable.{a} (X i))
    (g : (∐ X) ⟶ (∐ Y)) (s : Finset (Discrete A)) :
    ∃ (t : Finset (Discrete B)) (f : (∐ fun i : s => X i.1.as) ⟶ (∐ fun j : t => Y j.1.as)),
      Sigma.desc (fun i : s => Sigma.ι X i.1.as) ≫ g =
        f ≫ Sigma.desc (fun j : t => Sigma.ι Y j.1.as) := by
  classical
  have hex (i : s) : ∃ (T : Finset (Discrete B)) (q : X i.1.as ⟶ ∐ fun j : T => Y j.1.as),
      q ≫ Sigma.desc (fun j : T => Sigma.ι Y j.1.as) = Sigma.ι X i.1.as ≫ g := by
    let := hcompact i.1.as
    exact exists_finiteSubcoproduct_factorization Y (X i.1.as) (Sigma.ι X i.1.as ≫ g)
  let T (i : s) : Finset (Discrete B) := (hex i).choose
  let q (i : s) : X i.1.as ⟶ ∐ fun j : T i => Y j.1.as := (hex i).choose_spec.choose
  have hq (i : s) : q i ≫ Sigma.desc (fun j : T i => Sigma.ι Y j.1.as) =
      Sigma.ι X i.1.as ≫ g := (hex i).choose_spec.choose_spec
  let t : Finset (Discrete B) := Finset.univ.biUnion T
  let e (i : s) : (∐ fun j : T i => Y j.1.as) ⟶ (∐ fun j : t => Y j.1.as) :=
    Sigma.desc fun j => Sigma.ι (fun j : t => Y j.1.as)
      ⟨j.1, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, j.2⟩⟩
  have he (i : s) : e i ≫ Sigma.desc (fun j : t => Sigma.ι Y j.1.as) =
      Sigma.desc (fun j : T i => Sigma.ι Y j.1.as) := by
    apply Sigma.hom_ext
    intro j
    simp [e]
  refine ⟨t, Sigma.desc fun i => q i ≫ e i, ?_⟩
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc, Category.assoc,
    he, hq]

end Compact

section FilteredCokernels

variable {E : Type d} [Category.{a} E] [HasZeroMorphisms E] [HasColimitsOfSize.{a, a} E]

/-- The inclusion of a finite subcoproduct into the whole coproduct is a split monomorphism, the
retraction being the projection which kills the summands outside the finite subset. -/
public theorem isSplitMono_finiteSubcoproductsCocone_ι {A : Type a} (Y : A → E)
    (s : Finset (Discrete A)) :
    IsSplitMono ((finiteSubcoproductsCocone Y).ι.app s) := by
  classical
  let r : (∐ Y) ⟶ (∐ fun i : s => Y i.1.as) :=
    Sigma.desc fun i => if h : Discrete.mk i ∈ s then
      Sigma.ι (fun i : s => Y i.1.as) ⟨Discrete.mk i, h⟩ else 0
  refine ⟨⟨r, Sigma.hom_ext _ _ fun i => ?_⟩⟩
  change Sigma.ι (fun j : s => Y j.1.as) i ≫
      Sigma.desc (fun j : s => Sigma.ι Y j.1.as) ≫ r =
    Sigma.ι (fun j : s => Y j.1.as) i ≫ 𝟙 (∐ fun j : s => Y j.1.as)
  simp [r, i.2]

/-- **Pointwise cokernels commute with colimits.** If `g` is compatible with a family of maps `f`
between two diagrams with colimit cocones `l` and `n`, the cokernels of `f` form a diagram whose
colimit is the cokernel of `g`. -/
private theorem exists_isColimit_cokernel_of_isColimit {I : Type a} [SmallCategory I]
    {L N : I ⥤ E} {l : Cocone L} {n : Cocone N} (hl : IsColimit l) (hn : IsColimit n)
    (g : l.pt ⟶ n.pt) (f : ∀ i, L.obj i ⟶ N.obj i)
    (hf : ∀ i, l.ι.app i ≫ g = f i ≫ n.ι.app i)
    (hw : ∀ {i j : I} (h : i ⟶ j), L.map h ≫ f j = f i ≫ N.map h) :
    ∃ (D : I ⥤ E) (c : Cocone D), c.pt = cokernel g ∧ Nonempty (IsColimit c) ∧
      ∀ i, Nonempty (D.obj i ≅ cokernel (f i)) := by
  let D : I ⥤ E :=
    { obj i := cokernel (f i)
      map h := cokernel.map _ _ (L.map h) (N.map h) (hw h).symm
      map_id i := by
        apply coequalizer.hom_ext
        simp
      map_comp h k := by
        apply coequalizer.hom_ext
        simp [Category.assoc] }
  let π : N ⟶ D :=
    { app i := cokernel.π (f i)
      naturality i j h := by simp [D] }
  let c : Cocone D :=
    { pt := cokernel g
      ι :=
        { app i := cokernel.desc (f i) (n.ι.app i ≫ cokernel.π g) (by
            rw [← Category.assoc, ← hf, Category.assoc, cokernel.condition, comp_zero])
          naturality i j h := by
            apply coequalizer.hom_ext
            simp [D, Category.assoc] } }
  have hc : IsColimit c := by
    let liftCocone (s : Cocone D) : Cocone N :=
      { pt := s.pt
        ι := π ≫ s.ι }
    have kill (s : Cocone D) : g ≫ hn.desc (liftCocone s) = 0 := by
      apply hl.hom_ext
      intro i
      rw [← Category.assoc, hf, Category.assoc, hn.fac]
      simp [liftCocone, π]
    refine
      { desc := fun s => cokernel.desc g (hn.desc (liftCocone s)) (kill s)
        fac := fun s i => ?_
        uniq := fun s m hm => ?_ }
    · apply coequalizer.hom_ext
      simp only [Category.assoc, c, cokernel.π_desc_assoc, cokernel.π_desc]
      exact hn.fac (liftCocone s) i
    · apply coequalizer.hom_ext
      rw [cokernel.π_desc]
      apply hn.hom_ext
      intro i
      rw [hn.fac]
      change n.ι.app i ≫ cokernel.π g ≫ m = cokernel.π (f i) ≫ s.ι.app i
      calc
        n.ι.app i ≫ cokernel.π g ≫ m = cokernel.π (f i) ≫ c.ι.app i ≫ m := by
          rw [← Category.assoc, ← Category.assoc]
          congr 1
          exact (cokernel.π_desc _ _ _).symm
        _ = _ := by rw [hm]
  exact ⟨D, c, rfl, ⟨hc⟩, fun i => ⟨Iso.refl _⟩⟩

/-- **A cokernel of a map between coproducts is a filtered colimit of cokernels of maps between
finite subcoproducts.** Suppose every finite subcoproduct of the source maps into some finite
subcoproduct of the target compatibly with `g`. Then the pairs of finite subsets admitting such a
compatible map form a filtered index category, the cokernels of those restrictions of `g` form a
diagram over it, and its colimit is the cokernel of `g`.

The two projections from the index category to the finite subsets of the source, resp. target,
are final, so the coproducts are already the colimits of the restricted diagrams; the cokernel of
`g` is then the colimit of the pointwise cokernels, because the inclusion of a finite subcoproduct
of the target is a monomorphism, which is what makes the chosen restrictions of `g` into a natural
transformation. -/
public theorem exists_isFilteredColimit_cokernel_finiteSubcoproducts {A B : Type a} (X : A → E)
    (Y : B → E) (g : (∐ X) ⟶ (∐ Y))
    (hfin : ∀ s : Finset (Discrete A), ∃ t : Finset (Discrete B),
      ∃ f : (liftToFinsetObj (Discrete.functor X)).obj s ⟶
        (liftToFinsetObj (Discrete.functor Y)).obj t,
      (finiteSubcoproductsCocone X).ι.app s ≫ g =
        f ≫ (finiteSubcoproductsCocone Y).ι.app t) :
    ∃ (I : Type a) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ E) (c : Cocone D), c.pt = cokernel g ∧ Nonempty (IsColimit c) ∧
        ∀ i, ∃ (s : Finset (Discrete A)) (t : Finset (Discrete B))
          (f : (∐ fun j : s => X j.1.as) ⟶ (∐ fun j : t => Y j.1.as)),
          Nonempty (D.obj i ≅ cokernel f) := by
  classical
  let FX := liftToFinsetObj (Discrete.functor X)
  let FY := liftToFinsetObj (Discrete.functor Y)
  let cX := finiteSubcoproductsCocone X
  let cY := finiteSubcoproductsCocone Y
  let I := {p : Finset (Discrete A) × Finset (Discrete B) //
    ∃ f : FX.obj p.1 ⟶ FY.obj p.2, cX.ι.app p.1 ≫ g = f ≫ cY.ι.app p.2}
  have hex (s : Finset (Discrete A)) (t : Finset (Discrete B)) :
      ∃ i : I, s ⊆ i.1.1 ∧ t ⊆ i.1.2 := by
    obtain ⟨t', f, hf⟩ := hfin s
    refine ⟨⟨(s, t ∪ t'), f ≫ FY.map (homOfLE Finset.subset_union_right), ?_⟩,
      le_rfl, Finset.subset_union_left⟩
    rwa [Category.assoc, cY.w (homOfLE (Finset.subset_union_right : t' ⊆ t ∪ t'))]
  have : Nonempty I := ⟨(hex ∅ ∅).choose⟩
  have : IsDirectedOrder I := ⟨fun i j => by
    obtain ⟨k, hk₁, hk₂⟩ := hex (i.1.1 ∪ j.1.1) (i.1.2 ∪ j.1.2)
    exact ⟨k, ⟨Finset.subset_union_left.trans hk₁, Finset.subset_union_left.trans hk₂⟩,
      ⟨Finset.subset_union_right.trans hk₁, Finset.subset_union_right.trans hk₂⟩⟩⟩
  let pX : I ⥤ Finset (Discrete A) := (show Monotone (fun i : I => i.1.1) from
    fun _ _ h => h.1).functor
  let pY : I ⥤ Finset (Discrete B) := (show Monotone (fun i : I => i.1.2) from
    fun _ _ h => h.2).functor
  have : pX.Final := Functor.final_of_exists_of_isFiltered pX
    (fun s => by
      obtain ⟨i, hi, _⟩ := hex s ∅
      exact ⟨i, ⟨homOfLE hi⟩⟩)
    (fun {_ i} _ _ => ⟨i, 𝟙 _, Subsingleton.elim _ _⟩)
  have : pY.Final := Functor.final_of_exists_of_isFiltered pY
    (fun t => by
      obtain ⟨i, _, hi⟩ := hex ∅ t
      exact ⟨i, ⟨homOfLE hi⟩⟩)
    (fun {_ i} _ _ => ⟨i, 𝟙 _, Subsingleton.elim _ _⟩)
  let L := pX ⋙ FX
  let N := pY ⋙ FY
  let l : Cocone L := cX.whisker pX
  let n : Cocone N := cY.whisker pY
  let hl : IsColimit l := (Functor.Final.isColimitWhiskerEquiv pX cX).symm
    (isColimitFiniteSubproductsCocone X)
  let hn : IsColimit n := (Functor.Final.isColimitWhiskerEquiv pY cY).symm
    (isColimitFiniteSubproductsCocone Y)
  let f (i : I) : L.obj i ⟶ N.obj i := i.2.choose
  have hf (i : I) : l.ι.app i ≫ g = f i ≫ n.ι.app i := i.2.choose_spec
  have hw {i j : I} (h : i ⟶ j) : L.map h ≫ f j = f i ≫ N.map h := by
    have : Mono (n.ι.app j) := (isSplitMono_finiteSubcoproductsCocone_ι Y j.1.2).mono
    apply (cancel_mono (n.ι.app j)).1
    rw [Category.assoc, ← hf, ← Category.assoc, l.w, hf, Category.assoc, n.w]
  obtain ⟨D, c, hpt, hc, hD⟩ := exists_isColimit_cokernel_of_isColimit hl hn g f hf hw
  exact ⟨I, inferInstance, inferInstance, D, c, hpt, hc, fun i => ⟨i.1.1, i.1.2, f i, hD i⟩⟩

end FilteredCokernels

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]

attribute [local instance] smallEtaleHasSheafifyModuleMax
  smallEtaleHasColimitsOfSizeModuleMax

/-- A cokernel of a map between coproducts indexed by finite types, of extensions by zero at
étale objects satisfying `P`, is a finite shriek presentation: the index types are reindexed by
`Fin n`, and the universe lift occurring in
`AlgebraicGeometry.HasFiniteShriekPresentation` is a lift inside `u + 1`. -/
private theorem hasFiniteShriekPresentation_of_cokernel_iso
    (P : SmallEtale B X.1 X.property → Prop) {A₁ A₂ : Type (u + 1)} [Finite A₁] [Finite A₂]
    (U : A₂ → SmallEtale B X.1 X.property) (V : A₁ → SmallEtale B X.1 X.property)
    (hU : ∀ i, P (U i)) (hV : ∀ j, P (V j))
    (f : (∐ fun j => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (V j)) ⟶
      (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (U i)))
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (e : cokernel f ≅ G) :
    HasFiniteShriekPresentation.{u, u + 1, u + 1} B X Λ P G := by
  let := Fintype.ofFinite A₁
  let := Fintype.ofFinite A₂
  let a := (Fintype.equivFin A₁).symm
  let b := (Fintype.equivFin A₂).symm
  let eA := Sigma.reindex a (fun j => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (V j))
  let eB := Sigma.reindex b (fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (U i))
  refine ⟨Fintype.card A₂, Fintype.card A₁, U ∘ b, V ∘ a,
    fun i => hU _, fun j => hV _, eA.hom ≫ f ≫ eB.inv, ⟨?_⟩⟩
  refine (sheafToPresheaf (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{u + 1} Λ)).mapIso
    (cokernel.mapIso _ f eA eB
      (by rw [Category.assoc, Category.assoc, eB.inv_hom_id, Category.comp_id]) ≪≫ e) ≪≫ ?_
  exact (Functor.isoWhiskerLeft G.obj (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} Λ) ≪≫
    G.obj.rightUnitor).symm

variable [CompactSpace X.1] [QuasiSeparatedSpace X.1]

/-- **Stacks 093C for sheaves of `Λ`-modules on the small étale site.** Every sheaf of
`Λ`-modules on the small étale site of a scheme `X` is a filtered colimit of sheaves carrying a
finite shriek presentation by quasi-compact quasi-separated étale objects, that is, of cokernels
of maps between finite direct sums of the sheaves `j_{U!}\underline{\Lambda}_U` at such objects.

This is the source's own proof. Two applications of Stacks 093B part (2),
`AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_qcqs`, write `F` as the cokernel of a map
`g` between two direct sums of the sheaves `j_{U!}\underline{\Lambda}_U` at quasi-compact
quasi-separated étale objects: the first gives an epimorphism `p` onto `F`, the second an
epimorphism `q` onto the kernel of `p`, and `q ≫ ker p` has cokernel `F`. Those generators are
compact, by `AlgebraicGeometry.isFinitelyPresentable_moduleShriekConstant` together with
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`, so `g` restricts to maps between
finite subsums; and the cokernels of those restrictions form a filtered diagram with colimit the
cokernel of `g`, which is
`CategoryTheory.Limits.exists_isFilteredColimit_cokernel_finiteSubcoproducts`.

The quasi-compactness and quasi-separatedness of `X` are used only for the compactness of the
generators, which asks for
`AlgebraicGeometry.SmallEtale.hasFiniteQuasiCompactCoverings`; the generation step itself needs
neither. This discharges the hypothesis `h093C` of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf`, Stacks 03SA (3), which
carries the same two assumptions on `X`.

[Stacks Tag 093C](https://stacks.math.columbia.edu/tag/093C) part (2) is stated for an arbitrary
situation of Stacks 0937 and an arbitrary sheaf of rings by
`Stacks.Sites.isFilteredColimit_of_hasEnoughQuasiCompactObjects`, which carries the tag; this is
that statement at the small étale site with constant coefficients `Λ`, in the shriek spelling the
étale development consumes. -/
@[stacks 093C "part (2), sheaves of modules on the small étale site, shriek spelling"]
public theorem moduleSheavesAreFilteredColimitsOfPresentations :
    ModuleSheavesAreFilteredColimitsOfPresentations B X Λ := by
  intro F
  obtain ⟨A₂, U, hU, p, hp⟩ := exists_epi_sigma_moduleShriekConstant_qcqs B X Λ F
  let := hp
  obtain ⟨A₁, V, hV, q, hq⟩ :=
    exists_epi_sigma_moduleShriekConstant_qcqs B X Λ (kernel p)
  let := hq
  have hcolim : IsColimit (CokernelCofork.ofπ (f := q ≫ kernel.ι p) p
      (by rw [Category.assoc, kernel.condition, comp_zero])) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ p (kernel.condition p))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) q rfl
  have eF : cokernel (q ≫ kernel.ι p) ≅ F :=
    (colimit.isColimit _).coconePointUniqueUpToIso hcolim
  have hcompact (j : A₁) :
      IsFinitelyPresentable.{u + 1} (moduleShriekConstant.{u, u + 1, u + 1} B X Λ (V j)) :=
    isFinitelyPresentable_moduleShriekConstant B X Λ (V j)
      (SmallEtale.hasFiniteQuasiCompactCoverings B X (V j) (hV j).1 (hV j).2)
  obtain ⟨I, hcat, hfiltered, D, c, hpt, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_cokernel_finiteSubcoproducts
      (fun j => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (V j))
      (fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (U i)) (q ≫ kernel.ι p)
      (exists_finiteSubcoproduct_restriction _ _ hcompact (q ≫ kernel.ι p))
  let e' : c.pt ≅ F := eqToIso hpt ≪≫ eF
  refine ⟨I, hcat, hfiltered, D, c.ι ≫ (Functor.const I).map e'.hom,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext e' (fun i => by simp))⟩, ?_⟩
  intro i
  obtain ⟨s, t, f, ⟨ef⟩⟩ := hD i
  exact hasFiniteShriekPresentation_of_cokernel_iso B X Λ (IsQCQSEtaleObject B X)
    (fun i : t => U i.1.as) (fun j : s => V j.1.as)
    (fun i => hU _) (fun j => hV _) f (D.obj i) ef.symm

end AlgebraicGeometry

end
